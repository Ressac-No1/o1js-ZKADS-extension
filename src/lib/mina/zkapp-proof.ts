import { Pickles } from '../../snarky.js';
import {
  AccountUpdate,
  Authorization,
  FeePayerUnsigned,
  LazyProof,
  LazySignature,
  ZkappCommand,
  ZkappProverData,
  ZkappPublicInput,
  zkAppProver,
} from '../account_update.js';
import { assert } from '../gadgets/common.js';
import { MlArray } from '../ml/base.js';
import { MlFieldConstArray } from '../ml/fields.js';
import {
  Empty,
  Proof,
  dummyBase64Proof,
  methodArgumentsToVars,
} from '../proof_system.js';
import { runCircuit } from '../provable-context-debug.js';
import { Provable, memoizationContext } from '../provable.js';

export { addMissingProofs, runAsIfProver };

type AccountUpdateProved = AccountUpdate & {
  lazyAuthorization?: LazySignature;
};

type ZkappCommandProved = {
  feePayer: FeePayerUnsigned;
  accountUpdates: AccountUpdateProved[];
  memo: string;
};

async function addMissingProofs(
  zkappCommand: ZkappCommand,
  { proofsEnabled = true }
): Promise<{
  zkappCommand: ZkappCommandProved;
  proofs: (Proof<ZkappPublicInput, Empty> | undefined)[];
}> {
  let { feePayer, accountUpdates, memo } = zkappCommand;
  // compute proofs serially. in parallel would clash with our global variable
  // hacks
  let accountUpdatesProved: AccountUpdateProved[] = [];
  let proofs: (Proof<ZkappPublicInput, Empty> | undefined)[] = [];
  for (let i = 0; i < accountUpdates.length; i++) {
    let { accountUpdateProved, proof } = await addProof(
      zkappCommand,
      i,
      proofsEnabled
    );
    accountUpdatesProved.push(accountUpdateProved);
    proofs.push(proof);
  }
  return {
    zkappCommand: { feePayer, accountUpdates: accountUpdatesProved, memo },
    proofs,
  };
}

async function addProof(
  transaction: ZkappCommand,
  index: number,
  proofsEnabled: boolean
) {
  let accountUpdate = transaction.accountUpdates[index];
  accountUpdate = AccountUpdate.clone(accountUpdate);

  if (accountUpdate.lazyAuthorization?.kind !== 'lazy-proof') {
    return {
      accountUpdateProved: accountUpdate as AccountUpdateProved,
      proof: undefined,
    };
  }
  if (!proofsEnabled) {
    Authorization.setProof(accountUpdate, await dummyBase64Proof());
    return {
      accountUpdateProved: accountUpdate as AccountUpdateProved,
      proof: undefined,
    };
  }

  let lazyProof: LazyProof = accountUpdate.lazyAuthorization;
  let prover = getZkappProver(lazyProof);
  let proverData = { transaction, accountUpdate, index };
  let proof = await createZkappProof(prover, lazyProof, proverData);

  let accountUpdateProved = Authorization.setProof(
    accountUpdate,
    Pickles.proofToBase64Transaction(proof.proof)
  );
  return { accountUpdateProved, proof };
}

async function createZkappProof(
  prover: Pickles.Prover,
  {
    methodName,
    args,
    previousProofs,
    ZkappClass,
    memoized,
    blindingValue,
  }: LazyProof,
  { transaction, accountUpdate, index }: ZkappProverData
): Promise<Proof<ZkappPublicInput, Empty>> {
  let publicInput = accountUpdate.toPublicInput();
  let publicInputFields = MlFieldConstArray.to(
    ZkappPublicInput.toFields(publicInput)
  );

  let [, , proof] = await zkAppProver.run(
    [accountUpdate.publicKey, accountUpdate.tokenId, ...args],
    { transaction, accountUpdate, index },
    async () => {
      let id = memoizationContext.enter({
        memoized,
        currentIndex: 0,
        blindingValue,
      });
      try {
        return await prover(publicInputFields, MlArray.to(previousProofs));
      } catch (err) {
        console.error(`Error when proving ${ZkappClass.name}.${methodName}()`);
        throw err;
      } finally {
        memoizationContext.leave(id);
      }
    }
  );

  let maxProofsVerified = ZkappClass._maxProofsVerified!;
  const Proof = ZkappClass.Proof();
  return new Proof({
    publicInput,
    publicOutput: undefined,
    proof,
    maxProofsVerified,
  });
}

function getZkappProver({ methodName, ZkappClass }: LazyProof) {
  if (ZkappClass._provers === undefined)
    throw Error(
      `Cannot prove execution of ${methodName}(), no prover found. ` +
        `Try calling \`await ${ZkappClass.name}.compile()\` first, this will cache provers in the background.`
    );
  let provers = ZkappClass._provers;
  let methodError =
    `Error when computing proofs: Method ${methodName} not found. ` +
    `Make sure your environment supports decorators, and annotate with \`@method ${methodName}\`.`;
  if (ZkappClass._methods === undefined) throw Error(methodError);
  let i = ZkappClass._methods.findIndex((m) => m.methodName === methodName);
  if (i === -1) throw Error(methodError);
  return provers[i];
}

// for debugging prove/compile discrepancies
// TODO run this automatically when detecting some problem

function runAsIfProver(transaction: ZkappCommand, index: number) {
  let accountUpdate = transaction.accountUpdates[index];
  accountUpdate = AccountUpdate.clone(accountUpdate);

  assert(
    accountUpdate.lazyAuthorization?.kind === 'lazy-proof',
    'Account update is not associated with a provable method call'
  );

  let { methodName, ZkappClass, args, memoized, blindingValue } =
    accountUpdate.lazyAuthorization;
  let metadata = ZkappClass._methodMetadata?.[methodName];
  let methodIntf = ZkappClass._methods?.find(
    (m) => m.methodName === methodName
  );

  assert(
    metadata !== undefined && methodIntf !== undefined,
    `No metadata found for zkapp method ${methodName}()`
  );

  let publicInput = accountUpdate.toPublicInput();
  let proverData = { transaction, accountUpdate, index };

  runCircuit(
    () => {
      let id = memoizationContext.enter({
        memoized,
        currentIndex: 0,
        blindingValue,
      });
      try {
        let [pk, tid, ...otherArgs] = methodArgumentsToVars(
          [accountUpdate.publicKey, accountUpdate.tokenId, ...args],
          methodIntf!
        ).args;
        publicInput = Provable.witness(ZkappPublicInput, () => publicInput);

        let instance = new ZkappClass(pk, tid);
        (instance as any)[methodName](publicInput, ...otherArgs);
      } finally {
        memoizationContext.leave(id);
      }
    },
    {
      withWitness: true,
      snarkContext: { proverData, inAnalyze: true },
      expectedConstraints: metadata.expectedConstraints,
    }
  );
}
