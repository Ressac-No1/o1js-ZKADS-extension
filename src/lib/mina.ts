// This is for an account where any of a list of public keys can update the state

import { Circuit, Ledger, LedgerAccount } from '../snarky.js';
import { Field, Bool } from './core.js';
import { UInt32, UInt64 } from './int.js';
import { PrivateKey, PublicKey } from './signature.js';
import {
  addMissingProofs,
  addMissingSignatures,
  FeePayerUnsigned,
  ZkappCommand,
  zkappCommandToJson,
  AccountUpdate,
  ZkappStateLength,
  ZkappPublicInput,
  TokenId,
  CallForest,
  Authorization,
  SequenceEvents,
  Permissions,
} from './account_update.js';

import * as Fetch from './fetch.js';
import { assertPreconditionInvariants, NetworkValue } from './precondition.js';
import { cloneCircuitValue } from './circuit_value.js';
import { Proof, snarkContext, verify } from './proof_system.js';
import { Context } from './global-context.js';
import { emptyReceiptChainHash } from './hash.js';
import { SmartContract } from './zkapp.js';
import { invalidTransactionError } from './errors.js';
import { Types } from 'src/index.js';

export {
  createTransaction,
  BerkeleyQANet,
  Network,
  LocalBlockchain,
  currentTransaction,
  CurrentTransaction,
  setActiveInstance,
  transaction,
  sender,
  currentSlot,
  getAccount,
  hasAccount,
  getBalance,
  getNetworkState,
  accountCreationFee,
  sendTransaction,
  fetchEvents,
  getActions,
  FeePayerSpec,
  // for internal testing only
  filterGroups,
};
interface TransactionId {
  wait(options?: { maxAttempts?: number; interval?: number }): Promise<void>;
  hash(): string;
}

interface Transaction {
  /**
   * Transaction structure used to describe a state transition on the Mina blockchain.
   */
  transaction: ZkappCommand;
  /**
   * Returns a JSON representation of the {@link Transaction}.
   */
  toJSON(): string;
  /**
   * Returns a pretty-printed JSON representation of the {@link Transaction}.
   */
  toPretty(): any;
  /**
   * Returns the GraphQL query for the Mina daemon.
   */
  toGraphqlQuery(): string;
  /**
   * Signs all {@link AccountUpdate}s included in the {@link Transaction} that require a signature.
   *
   * {@link AccountUpdate}s that require a signature can be specified with `{AccountUpdate|SmartContract}.requireSignature()`.
   *
   * @param additionalKeys The list of keys that should be used to sign the {@link Transaction}
   */
  sign(additionalKeys?: PrivateKey[]): Transaction;
  /**
   * Generates proofs for the {@link Transaction}.
   *
   * This can take some time.
   */
  prove(): Promise<(Proof<ZkappPublicInput> | undefined)[]>;
  /**
   * Sends the {@link Transaction} to the network.
   */
  send(): Promise<TransactionId>;
}

type Account = Fetch.Account;

type FetchMode = 'fetch' | 'cached' | 'test';
type CurrentTransaction = {
  sender?: PublicKey;
  accountUpdates: AccountUpdate[];
  fetchMode: FetchMode;
  isFinalRunOutsideCircuit: boolean;
  numberOfRuns: 0 | 1 | undefined;
};

let currentTransaction = Context.create<CurrentTransaction>();

/**
 * Allows you to specify information about the fee payer account and the transaction.
 */
type FeePayerSpec =
  | PublicKey
  | {
      sender: PublicKey;
      fee?: number | string | UInt64;
      memo?: string;
      nonce?: number;
    }
  | undefined;

type DeprecatedFeePayerSpec =
  | PublicKey
  | PrivateKey
  | ((
      | {
          feePayerKey: PrivateKey;
          sender?: PublicKey;
        }
      | {
          feePayerKey?: PrivateKey;
          sender: PublicKey;
        }
    ) & {
      fee?: number | string | UInt64;
      memo?: string;
      nonce?: number;
    })
  | undefined;

function reportGetAccountError(publicKey: string, tokenId: string) {
  if (tokenId === TokenId.toBase58(TokenId.default)) {
    return `getAccount: Could not find account for public key ${publicKey}`;
  } else {
    return `getAccount: Could not find account for public key ${publicKey} with the tokenId ${tokenId}`;
  }
}

function createTransaction(
  feePayer: DeprecatedFeePayerSpec,
  f: () => unknown,
  numberOfRuns: 0 | 1 | undefined,
  {
    fetchMode = 'cached' as FetchMode,
    isFinalRunOutsideCircuit = true,
    proofsEnabled = true,
  } = {}
): Transaction {
  if (currentTransaction.has()) {
    throw new Error('Cannot start new transaction within another transaction');
  }
  let feePayerSpec: {
    sender?: PublicKey;
    feePayerKey?: PrivateKey;
    fee?: number | string | UInt64;
    memo?: string;
    nonce?: number;
  };
  if (feePayer === undefined) {
    feePayerSpec = {};
  } else if (feePayer instanceof PrivateKey) {
    feePayerSpec = { feePayerKey: feePayer, sender: feePayer.toPublicKey() };
  } else if (feePayer instanceof PublicKey) {
    feePayerSpec = { sender: feePayer };
  } else {
    feePayerSpec = feePayer;
    if (feePayerSpec.sender === undefined)
      feePayerSpec.sender = feePayerSpec.feePayerKey?.toPublicKey();
  }
  let { feePayerKey, sender, fee, memo = '', nonce } = feePayerSpec;

  let transactionId = currentTransaction.enter({
    sender,
    accountUpdates: [],
    fetchMode,
    isFinalRunOutsideCircuit,
    numberOfRuns,
  });

  // run circuit
  // we have this while(true) loop because one of the smart contracts we're calling inside `f` might be calling
  // SmartContract.analyzeMethods, which would be running its methods again inside `Circuit.constraintSystem`, which
  // would throw an error when nested inside `Circuit.runAndCheck`. So if that happens, we have to run `analyzeMethods` first
  // and retry `Circuit.runAndCheck(f)`. Since at this point in the function, we don't know which smart contracts are involved,
  // we created that hack with a `bootstrap()` function that analyzeMethods sticks on the error, to call itself again.
  try {
    let err: any;
    while (true) {
      if (err !== undefined) err.bootstrap();
      try {
        snarkContext.runWith({ inRunAndCheck: true }, () =>
          Circuit.runAndCheck(f)
        );
        break;
      } catch (err_) {
        if ((err_ as any)?.bootstrap) err = err_;
        else throw err_;
      }
    }
  } catch (err) {
    currentTransaction.leave(transactionId);
    throw err;
  }
  let accountUpdates = currentTransaction.get().accountUpdates;
  CallForest.addCallers(accountUpdates);
  accountUpdates = CallForest.toFlatList(accountUpdates);

  try {
    // check that on-chain values weren't used without setting a precondition
    for (let accountUpdate of accountUpdates) {
      assertPreconditionInvariants(accountUpdate);
    }
  } catch (err) {
    currentTransaction.leave(transactionId);
    throw err;
  }

  let feePayerAccountUpdate: FeePayerUnsigned;
  if (sender !== undefined) {
    // if senderKey is provided, fetch account to get nonce and mark to be signed
    let nonce_;
    let senderAccount = getAccount(sender, TokenId.default);

    if (nonce === undefined) {
      nonce_ = senderAccount.nonce;
    } else {
      nonce_ = UInt32.from(nonce);
      senderAccount.nonce = nonce_;
      Fetch.addCachedAccount({
        nonce: senderAccount.nonce,
        publicKey: senderAccount.publicKey,
        tokenId: senderAccount.tokenId.toString(),
        balance: senderAccount.balance,
        zkapp: {
          appState: senderAccount.appState ?? [],
        },
      });
    }
    feePayerAccountUpdate = AccountUpdate.defaultFeePayer(sender, nonce_);
    if (feePayerKey !== undefined)
      feePayerAccountUpdate.lazyAuthorization!.privateKey = feePayerKey;
    if (fee !== undefined) {
      feePayerAccountUpdate.body.fee =
        fee instanceof UInt64 ? fee : UInt64.from(String(fee));
    }
  } else {
    // otherwise use a dummy fee payer that has to be filled in later
    feePayerAccountUpdate = AccountUpdate.dummyFeePayer();
  }

  let transaction: ZkappCommand = {
    accountUpdates,
    feePayer: feePayerAccountUpdate,
    memo,
  };

  currentTransaction.leave(transactionId);
  let self: Transaction = {
    transaction,
    sign(additionalKeys?: PrivateKey[]) {
      self.transaction = addMissingSignatures(self.transaction, additionalKeys);
      return self;
    },
    async prove() {
      let { zkappCommand, proofs } = await addMissingProofs(self.transaction, {
        proofsEnabled,
      });
      self.transaction = zkappCommand;
      return proofs;
    },
    toJSON() {
      let json = zkappCommandToJson(self.transaction);
      return JSON.stringify(json);
    },
    toPretty() {
      return ZkappCommand.toPretty(self.transaction);
    },
    toGraphqlQuery() {
      return Fetch.sendZkappQuery(self.toJSON());
    },
    async send() {
      return await sendTransaction(self);
    },
  };
  return self;
}

interface Mina {
  transaction(
    sender: DeprecatedFeePayerSpec,
    f: () => void
  ): Promise<Transaction>;
  currentSlot(): UInt32;
  hasAccount(publicKey: PublicKey, tokenId?: Field): boolean;
  getAccount(publicKey: PublicKey, tokenId?: Field): Account;
  getNetworkState(): NetworkValue;
  accountCreationFee(): UInt64;
  sendTransaction(transaction: Transaction): Promise<TransactionId>;
  fetchEvents: (publicKey: PublicKey, tokenId?: Field) => any;
  getActions: (
    publicKey: PublicKey,
    tokenId?: Field
  ) => { hash: string; actions: string[][] }[];
}

const defaultAccountCreationFee = 1_000_000_000;

/**
 * A mock Mina blockchain running locally and useful for testing.
 */
function LocalBlockchain({
  accountCreationFee = defaultAccountCreationFee as string | number,
  proofsEnabled = true,
  enforceTransactionLimits = true,
} = {}) {
  const msPerSlot = 3 * 60 * 1000;
  const startTime = new Date().valueOf();

  const ledger = Ledger.create([]);

  let networkState = defaultNetworkState();

  function addAccount(pk: PublicKey, balance: string) {
    ledger.addAccount(pk, balance);
  }

  let testAccounts: {
    publicKey: PublicKey;
    privateKey: PrivateKey;
  }[] = [];

  for (let i = 0; i < 10; ++i) {
    let MINA = 10n ** 9n;
    const largeValue = 1000n * MINA;
    const k = PrivateKey.random();
    const pk = k.toPublicKey();
    addAccount(pk, largeValue.toString());
    testAccounts.push({ privateKey: k, publicKey: pk });
  }

  const events: Record<string, any> = {};
  const actions: Record<string, any> = {};

  return {
    accountCreationFee: () => UInt64.from(accountCreationFee),
    currentSlot() {
      return UInt32.from(
        Math.ceil((new Date().valueOf() - startTime) / msPerSlot)
      );
    },
    hasAccount(publicKey: PublicKey, tokenId: Field = TokenId.default) {
      return !!ledger.getAccount(publicKey, tokenId);
    },
    getAccount(
      publicKey: PublicKey,
      tokenId: Field = TokenId.default
    ): Account {
      let ledgerAccount = ledger.getAccount(publicKey, tokenId);
      if (ledgerAccount == undefined) {
        throw new Error(
          reportGetAccountError(publicKey.toBase58(), TokenId.toBase58(tokenId))
        );
      } else {
        let { timing } = ledgerAccount;
        return {
          publicKey: publicKey,
          tokenId,
          balance: new UInt64(ledgerAccount.balance.value),
          nonce: new UInt32(ledgerAccount.nonce.value),
          appState:
            ledgerAccount.zkapp?.appState ??
            Array(ZkappStateLength).fill(Field(0)),
          tokenSymbol: ledgerAccount.tokenSymbol,
          receiptChainHash: ledgerAccount.receiptChainHash,
          provedState: Bool(ledgerAccount.zkapp?.provedState ?? false),
          delegate:
            ledgerAccount.delegate && PublicKey.from(ledgerAccount.delegate),
          sequenceState:
            ledgerAccount.zkapp?.sequenceState[0] ??
            SequenceEvents.emptySequenceState(),
          permissions: Permissions.fromJSON(ledgerAccount.permissions),
          timing: {
            isTimed: timing.isTimed,
            initialMinimumBalance: UInt64.fromObject(
              timing.initialMinimumBalance
            ),
            cliffAmount: UInt64.fromObject(timing.cliffAmount),
            cliffTime: UInt32.fromObject(timing.cliffTime),
            vestingPeriod: UInt32.fromObject(timing.vestingPeriod),
            vestingIncrement: UInt64.fromObject(timing.vestingIncrement),
          },
          verificationKey: ledgerAccount.zkapp?.verificationKey?.data,
        };
      }
    },
    getNetworkState() {
      return networkState;
    },
    async sendTransaction(txn: Transaction) {
      txn.sign();

      let commitments = Ledger.transactionCommitments(
        JSON.stringify(zkappCommandToJson(txn.transaction))
      );

      if (enforceTransactionLimits)
        verifyTransactionLimits(txn.transaction.accountUpdates);

      for (const update of txn.transaction.accountUpdates) {
        let account = ledger.getAccount(
          update.body.publicKey,
          update.body.tokenId
        );
        if (account) {
          await verifyAccountUpdate(
            account!,
            update,
            commitments,
            proofsEnabled
          );
        }
      }

      let zkappCommandJson = zkappCommandToJson(txn.transaction);
      try {
        ledger.applyJsonTransaction(
          JSON.stringify(zkappCommandJson),
          String(accountCreationFee),
          JSON.stringify(networkState)
        );
      } catch (err: any) {
        try {
          // reverse errors so they match order of account updates
          // TODO: label updates, and try to give precise explanations about what went wrong
          let errors = JSON.parse(err.message);
          err.message = invalidTransactionError(txn.transaction, errors, {
            accountCreationFee,
          });
        } finally {
          throw err;
        }
      }

      // fetches all events from the transaction and stores them
      // events are identified and associated with a publicKey and tokenId
      zkappCommandJson.accountUpdates.forEach((p) => {
        let addr = p.body.publicKey;
        let tokenId = p.body.tokenId;
        if (events[addr] === undefined) {
          events[addr] = {};
        }
        if (p.body.events.length > 0) {
          if (events[addr][tokenId] === undefined) {
            events[addr][tokenId] = [];
          }
          events[addr][tokenId].push({
            events: p.body.events,
            slot: networkState.globalSlotSinceGenesis.toString(),
          });
        }

        // actions/sequencing events

        // gets the index of the most up to date sequence state from our sequence list
        let n = actions[addr]?.[tokenId]?.length ?? 1;

        // most recent sequence state
        let sequenceState = actions?.[addr]?.[tokenId]?.[n - 1]?.hash;

        // if there exists no hash, this means we initialize our latest hash with the empty state
        let latestActionsHash =
          sequenceState === undefined
            ? SequenceEvents.emptySequenceState()
            : Ledger.fieldOfBase58(sequenceState);

        let actionList = p.body.actions;
        let eventsHash = SequenceEvents.hash(
          actionList.map((e) => e.map((f) => Field(f)))
        );

        if (actions[addr] === undefined) {
          actions[addr] = {};
        }
        if (p.body.actions.length > 0) {
          latestActionsHash = SequenceEvents.updateSequenceState(
            latestActionsHash,
            eventsHash
          );
          if (actions[addr][tokenId] === undefined) {
            actions[addr][tokenId] = [];
          }
          actions[addr][tokenId].push({
            actions: actionList,
            hash: Ledger.fieldToBase58(latestActionsHash),
          });
        }
      });
      return {
        wait: async (_options?: {
          maxAttempts?: number;
          interval?: number;
        }) => {
          console.log(
            'Info: Waiting for inclusion in a block is not supported for LocalBlockchain.'
          );
        },
        hash: (): string => {
          const message =
            'Info: Txn Hash retrieving is not supported for LocalBlockchain.';
          console.log(message);
          return message;
        },
      };
    },
    async transaction(sender: DeprecatedFeePayerSpec, f: () => void) {
      // bad hack: run transaction just to see whether it creates proofs
      // if it doesn't, this is the last chance to run SmartContract.runOutsideCircuit, which is supposed to run only once
      // TODO: this has obvious holes if multiple zkapps are involved, but not relevant currently because we can't prove with multiple account updates
      // and hopefully with upcoming work by Matt we can just run everything in the prover, and nowhere else
      let tx = createTransaction(sender, f, 0, {
        isFinalRunOutsideCircuit: false,
        proofsEnabled,
      });
      let hasProofs = tx.transaction.accountUpdates.some(
        Authorization.hasLazyProof
      );
      return createTransaction(sender, f, 1, {
        isFinalRunOutsideCircuit: !hasProofs,
        proofsEnabled,
      });
    },
    applyJsonTransaction(json: string) {
      return ledger.applyJsonTransaction(
        json,
        String(accountCreationFee),
        JSON.stringify(networkState)
      );
    },
    async fetchEvents(
      publicKey: PublicKey,
      tokenId: Field = TokenId.default
    ): Promise<any[]> {
      return events?.[publicKey.toBase58()]?.[TokenId.toBase58(tokenId)] ?? [];
    },
    getActions(
      publicKey: PublicKey,
      tokenId: Field = TokenId.default
    ): { hash: string; actions: string[][] }[] {
      return (
        actions?.[publicKey.toBase58()]?.[Ledger.fieldToBase58(tokenId)] ?? []
      );
    },
    addAccount,
    /**
     * An array of 10 test accounts that have been pre-filled with
     * 30000000000 units of currency.
     */
    testAccounts,
    setGlobalSlot(slot: UInt32 | number) {
      networkState.globalSlotSinceGenesis = UInt32.from(slot);
      let difference = networkState.globalSlotSinceGenesis.sub(slot);
    },
    incrementGlobalSlot(increment: UInt32 | number) {
      networkState.globalSlotSinceGenesis =
        networkState.globalSlotSinceGenesis.add(increment);
    },
    setBlockchainLength(height: UInt32) {
      networkState.blockchainLength = height;
    },
    setTotalCurrency(currency: UInt64) {
      networkState.totalCurrency = currency;
    },
    setProofsEnabled(newProofsEnabled: boolean) {
      proofsEnabled = newProofsEnabled;
    },
  };
}

/**
 * Represents the Mina blockchain running on a real network
 */
function Network(graphqlEndpoint: string): Mina {
  let accountCreationFee = UInt64.from(defaultAccountCreationFee);
  Fetch.setGraphqlEndpoint(graphqlEndpoint);
  return {
    accountCreationFee: () => accountCreationFee,
    currentSlot() {
      throw Error(
        'currentSlot() is not implemented yet for remote blockchains.'
      );
    },
    hasAccount(publicKey: PublicKey, tokenId: Field = TokenId.default) {
      if (
        !currentTransaction.has() ||
        currentTransaction.get().fetchMode === 'cached'
      ) {
        return !!Fetch.getCachedAccount(publicKey, tokenId, graphqlEndpoint);
      }
      return false;
    },
    getAccount(publicKey: PublicKey, tokenId: Field = TokenId.default) {
      if (currentTransaction()?.fetchMode === 'test') {
        Fetch.markAccountToBeFetched(publicKey, tokenId, graphqlEndpoint);
        let account = Fetch.getCachedAccount(
          publicKey,
          tokenId,
          graphqlEndpoint
        );
        return account ?? dummyAccount(publicKey);
      }
      if (
        !currentTransaction.has() ||
        currentTransaction.get().fetchMode === 'cached'
      ) {
        let account = Fetch.getCachedAccount(
          publicKey,
          tokenId,
          graphqlEndpoint
        );
        if (account !== undefined) return account;
      }
      throw Error(
        `${reportGetAccountError(
          publicKey.toBase58(),
          TokenId.toBase58(tokenId)
        )}\nGraphql endpoint: ${graphqlEndpoint}`
      );
    },
    getNetworkState() {
      if (currentTransaction()?.fetchMode === 'test') {
        Fetch.markNetworkToBeFetched(graphqlEndpoint);
        let network = Fetch.getCachedNetwork(graphqlEndpoint);
        return network ?? defaultNetworkState();
      }
      if (
        !currentTransaction.has() ||
        currentTransaction.get().fetchMode === 'cached'
      ) {
        let network = Fetch.getCachedNetwork(graphqlEndpoint);
        if (network !== undefined) return network;
      }
      throw Error(
        `getNetworkState: Could not fetch network state from graphql endpoint ${graphqlEndpoint}`
      );
    },
    async sendTransaction(txn: Transaction) {
      txn.sign();

      verifyTransactionLimits(txn.transaction.accountUpdates);

      let [response, error] = await Fetch.sendZkapp(txn.toJSON());
      let errors: any[] | undefined;
      if (error === undefined) {
        if (response!.data === null && (response as any).errors?.length > 0) {
          console.log(
            'got graphql errors',
            JSON.stringify((response as any).errors, null, 2)
          );
          errors = (response as any).errors;
        }
      } else {
        console.log('got fetch error', error);
        errors = [error];
      }

      let maxAttempts: number;
      let attempts = 0;
      let interval: number;

      return {
        data: response?.data,
        errors,
        async wait(options?: { maxAttempts?: number; interval?: number }) {
          // default is 45 attempts * 20s each = 15min
          // the block time on berkeley is currently longer than the average 3-4min, so its better to target a higher block time
          // fetching an update every 20s is more than enough with a current block time of 3min
          maxAttempts = options?.maxAttempts ?? 45;
          interval = options?.interval ?? 20000;

          const executePoll = async (
            resolve: () => void,
            reject: (err: Error) => void | Error
          ) => {
            let txId = response?.data?.sendZkapp?.zkapp?.id;
            let res = await Fetch.fetchTransactionStatus(txId);
            attempts++;
            if (res === 'INCLUDED') {
              return resolve();
            } else if (maxAttempts && attempts === maxAttempts) {
              return reject(
                new Error(
                  `Exceeded max attempts. TransactionId: ${txId}, attempts: ${attempts}, last received status: ${res}`
                )
              );
            } else {
              setTimeout(executePoll, interval, resolve, reject);
            }
          };

          return new Promise(executePoll);
        },
        hash() {
          return response?.data?.sendZkapp?.zkapp?.hash;
        },
      };
    },
    async transaction(sender: DeprecatedFeePayerSpec, f: () => void) {
      let tx = createTransaction(sender, f, 0, {
        fetchMode: 'test',
        isFinalRunOutsideCircuit: false,
      });
      await Fetch.fetchMissingData(graphqlEndpoint);
      let hasProofs = tx.transaction.accountUpdates.some(
        Authorization.hasLazyProof
      );
      return createTransaction(sender, f, 1, {
        fetchMode: 'cached',
        isFinalRunOutsideCircuit: !hasProofs,
      });
    },
    async fetchEvents() {
      throw Error(
        'fetchEvents() is not implemented yet for remote blockchains.'
      );
    },
    getActions() {
      throw Error(
        'fetchEvents() is not implemented yet for remote blockchains.'
      );
    },
  };
}

/**
 *
 * @deprecated This is deprecated in favor of {@link Mina.Network}, which is exactly the same function.
 * The name `BerkeleyQANet` was misleading because it suggested that this is specific to a particular network.
 */
function BerkeleyQANet(graphqlEndpoint: string) {
  return Network(graphqlEndpoint);
}

let activeInstance: Mina = {
  accountCreationFee: () => UInt64.from(defaultAccountCreationFee),
  currentSlot: () => {
    throw new Error('must call Mina.setActiveInstance first');
  },
  hasAccount(publicKey: PublicKey, tokenId: Field = TokenId.default) {
    if (
      !currentTransaction.has() ||
      currentTransaction.get().fetchMode === 'cached'
    ) {
      return !!Fetch.getCachedAccount(
        publicKey,
        tokenId,
        Fetch.defaultGraphqlEndpoint
      );
    }
    return false;
  },
  getAccount(publicKey: PublicKey, tokenId: Field = TokenId.default) {
    if (currentTransaction()?.fetchMode === 'test') {
      Fetch.markAccountToBeFetched(
        publicKey,
        tokenId,
        Fetch.defaultGraphqlEndpoint
      );
      return dummyAccount(publicKey);
    }
    if (
      !currentTransaction.has() ||
      currentTransaction.get().fetchMode === 'cached'
    ) {
      let account = Fetch.getCachedAccount(
        publicKey,
        tokenId,
        Fetch.defaultGraphqlEndpoint
      );
      if (account === undefined)
        throw Error(
          `${reportGetAccountError(
            publicKey.toBase58(),
            TokenId.toBase58(tokenId)
          )}\n\nEither call Mina.setActiveInstance first or explicitly add the account with addCachedAccount`
        );
      return account;
    }
    throw new Error('must call Mina.setActiveInstance first');
  },
  getNetworkState() {
    throw new Error('must call Mina.setActiveInstance first');
  },
  sendTransaction() {
    throw new Error('must call Mina.setActiveInstance first');
  },
  async transaction(sender: DeprecatedFeePayerSpec, f: () => void) {
    return createTransaction(sender, f, 0);
  },
  fetchEvents() {
    throw Error('must call Mina.setActiveInstance first');
  },
  getActions() {
    throw Error('must call Mina.setActiveInstance first');
  },
};

/**
 * Set the currently used Mina instance.
 */
function setActiveInstance(m: Mina) {
  activeInstance = m;
}

/**
 * Construct a smart contract transaction. Within the callback passed to this function,
 * you can call into the methods of smart contracts.
 *
 * ```
 * let tx = await Mina.transaction(sender, () => {
 *   myZkapp.update();
 *   someOtherZkapp.someOtherMethod();
 * });
 * ```
 *
 * @return A transaction that can subsequently be submitted to the chain.
 */
function transaction(sender: FeePayerSpec, f: () => void): Promise<Transaction>;
function transaction(f: () => void): Promise<Transaction>;
/**
 * @deprecated It's deprecated to pass in the fee payer's private key. Pass in the public key instead.
 * ```
 * // good
 * Mina.transaction(publicKey, ...);
 * Mina.transaction({ sender: publicKey }, ...);
 *
 * // deprecated
 * Mina.transaction(privateKey, ...);
 * Mina.transaction({ feePayerKey: privateKey }, ...);
 * ```
 */
function transaction(
  sender: DeprecatedFeePayerSpec,
  f: () => void
): Promise<Transaction>;
function transaction(
  senderOrF: DeprecatedFeePayerSpec | (() => void),
  fOrUndefined?: () => void
): Promise<Transaction> {
  let sender: DeprecatedFeePayerSpec;
  let f: () => void;
  if (fOrUndefined !== undefined) {
    sender = senderOrF as DeprecatedFeePayerSpec;
    f = fOrUndefined;
  } else {
    sender = undefined;
    f = senderOrF as () => void;
  }
  return activeInstance.transaction(sender, f);
}

/**
 * Returns the public key of the current transaction's sender account.
 *
 * Throws an error if not inside a transaction, or the sender wasn't passed in.
 */
function sender() {
  let tx = currentTransaction();
  if (tx === undefined)
    throw Error(
      `The sender is not available outside a transaction. Make sure you only use it within \`Mina.transaction\` blocks or smart contract methods.`
    );
  let sender = currentTransaction()?.sender;
  if (sender === undefined)
    throw Error(
      `The sender is not available, because the transaction block was created without the optional \`sender\` argument.
Here's an example for how to pass in the sender and make it available:

Mina.transaction(sender, // <-- pass in sender's public key here
() => {
  // methods can use this.sender
});
`
    );
  return sender;
}

/**
 * @return The current slot number, according to the active Mina instance.
 */
function currentSlot(): UInt32 {
  return activeInstance.currentSlot();
}

/**
 * @return The account data associated to the given public key.
 */
function getAccount(publicKey: PublicKey, tokenId?: Field): Account {
  return activeInstance.getAccount(publicKey, tokenId);
}

/**
 * Checks if an account exists within the ledger.
 */
function hasAccount(publicKey: PublicKey, tokenId?: Field): boolean {
  return activeInstance.hasAccount(publicKey, tokenId);
}

/**
 * @return Data associated with the current state of the Mina network.
 */
function getNetworkState() {
  return activeInstance.getNetworkState();
}

/**
 * @return The balance associated to the given public key.
 */
function getBalance(publicKey: PublicKey, tokenId?: Field) {
  return activeInstance.getAccount(publicKey, tokenId).balance;
}

/**
 * Returns the default account creation fee.
 */
function accountCreationFee() {
  return activeInstance.accountCreationFee();
}

async function sendTransaction(txn: Transaction) {
  return await activeInstance.sendTransaction(txn);
}

/**
 * @return A list of emitted events associated to the given public key.
 */
async function fetchEvents(publicKey: PublicKey, tokenId: Field) {
  return await activeInstance.fetchEvents(publicKey, tokenId);
}

/**
 * @return A list of emitted sequencing actions associated to the given public key.
 */
function getActions(publicKey: PublicKey, tokenId: Field) {
  return activeInstance.getActions(publicKey, tokenId);
}

function dummyAccount(pubkey?: PublicKey): Account {
  return {
    balance: UInt64.zero,
    nonce: UInt32.zero,
    publicKey: pubkey ?? PublicKey.empty(),
    tokenId: TokenId.default,
    appState: Array(ZkappStateLength).fill(Field(0)),
    tokenSymbol: '',
    provedState: Bool(false),
    receiptChainHash: emptyReceiptChainHash(),
    delegate: undefined,
    sequenceState: SequenceEvents.emptySequenceState(),
  };
}

function defaultNetworkState(): NetworkValue {
  let epochData: NetworkValue['stakingEpochData'] = {
    ledger: { hash: Field(0), totalCurrency: UInt64.zero },
    seed: Field(0),
    startCheckpoint: Field(0),
    lockCheckpoint: Field(0),
    epochLength: UInt32.zero,
  };
  return {
    snarkedLedgerHash: Field(0),
    blockchainLength: UInt32.zero,
    minWindowDensity: UInt32.zero,
    totalCurrency: UInt64.zero,
    globalSlotSinceGenesis: UInt32.zero,
    stakingEpochData: epochData,
    nextEpochData: cloneCircuitValue(epochData),
  };
}

async function verifyAccountUpdate(
  account: LedgerAccount,
  accountUpdate: AccountUpdate,
  transactionCommitments: {
    commitment: Field;
    fullCommitment: Field;
  },
  proofsEnabled: boolean
): Promise<void> {
  let perm = account.permissions;

  let { commitment, fullCommitment } = transactionCommitments;

  // we are essentially only checking if the update is empty or an actual update
  function includesChange(val: any): boolean {
    if (Array.isArray(val)) {
      return !val.every((v) => v === null);
    } else {
      return val != null;
    }
  }

  function permissionForUpdate(key: string): Types.Json.AuthRequired {
    switch (key) {
      case 'appState':
        return perm.editState;
      case 'delegate':
        return perm.setDelegate;
      case 'verificationKey':
        return perm.setVerificationKey;
      case 'permissions':
        return perm.setPermissions;
      case 'zkappUri':
        return perm.setZkappUri;
      case 'tokenSymbol':
        return perm.setTokenSymbol;
      case 'timing':
        return 'None';
      case 'votingFor':
        return perm.setVotingFor;
      case 'sequenceEvents':
        return perm.editSequenceState;
      case 'incrementNonce':
        return perm.incrementNonce;
      case 'send':
        return perm.send;
      case 'receive':
        return perm.receive;
      default:
        throw Error(`Invalid permission for field ${key}: does not exist.`);
    }
  }

  const update = accountUpdate.toJSON().body.update;

  let errorTrace = '';

  let isValidProof = false;
  let isValidSignature = false;

  // we don't check if proofs aren't enabled
  if (!proofsEnabled) isValidProof = true;

  if (accountUpdate.authorization.proof && proofsEnabled) {
    try {
      let publicInput = accountUpdate.toPublicInput();
      let publicInputFields = ZkappPublicInput.toFields(publicInput);

      const proof = SmartContract.Proof().fromJSON({
        maxProofsVerified: 2,
        proof: accountUpdate.authorization.proof!,
        publicInput: publicInputFields.map((f) => f.toString()),
      });

      let verificationKey = account.zkapp?.verificationKey?.data!;
      isValidProof = await verify(proof.toJSON(), verificationKey);
      if (!isValidProof) {
        throw Error(
          `Invalid proof for account update\n${JSON.stringify(update)}`
        );
      }
    } catch (error) {
      errorTrace += '\n\n' + (error as Error).message;
      isValidProof = false;
    }
  }

  if (accountUpdate.authorization.signature) {
    let txC = accountUpdate.body.useFullCommitment.toBoolean()
      ? fullCommitment
      : commitment;

    // checking permissions and authorization for each party individually
    try {
      isValidSignature = Ledger.checkAccountUpdateSignature(
        JSON.stringify(accountUpdate.toJSON()),
        txC
      );
    } catch (error) {
      errorTrace += '\n\n' + (error as Error).message;
      isValidSignature = false;
    }
  }

  let verified = false;

  function checkPermission(p: Types.Json.AuthRequired, field: string) {
    if (p == 'None') return;

    if (p == 'Impossible') {
      throw Error(
        `Transaction verification failed: Cannot update field '${field}' because permission for this field is '${p}'`
      );
    }

    if (p == 'Signature' || p == 'Either') {
      verified ||= isValidSignature;
    }

    if (p == 'Proof' || p == 'Either') {
      verified ||= isValidProof;
    }

    if (!verified) {
      throw Error(
        `Transaction verification failed: Cannot update field '${field}' because permission for this field is '${p}', but the required authorization was not provided or is invalid.
        ${errorTrace != '' ? 'Error trace: ' + errorTrace : ''}`
      );
    }
  }

  // goes through the update field on a transaction
  Object.entries(update).forEach(([key, value]) => {
    if (includesChange(value)) {
      let p = permissionForUpdate(key);
      checkPermission(p, key);
    }
  });

  // checks the sequence events (which result in an updated sequence state)
  if (accountUpdate.body.actions.data.length > 0) {
    let p = permissionForUpdate('sequenceEvents');
    checkPermission(p, 'sequenceEvents');
  }

  if (accountUpdate.body.incrementNonce.toBoolean()) {
    let p = permissionForUpdate('incrementNonce');
    checkPermission(p, 'incrementNonce');
  }

  // this checks for an edge case where an account update can be approved using proofs but
  // a) the proof is invalid (bad verification key)
  // and b) there are no state changes initiate so no permissions will be checked
  // however, if the verification key changes, the proof should still be invalid
  if (errorTrace && !verified) {
    throw Error(
      `One or more proofs were invalid and no other form of authorization was provided.\n${errorTrace}`
    );
  }
}

function verifyTransactionLimits(accountUpdates: AccountUpdate[]) {
  // constants used to calculate cost of a transaction - originally defined in the genesis_constants file in the mina repo
  const proofCost = 10.26;
  const signedPairCost = 10.08;
  const signedSingleCost = 9.14;
  const costLimit = 69.45;

  // constants that define the maximum number of events in one transaction
  const maxSequenceEventElements = 16;
  const maxEventElements = 16;

  let eventElements = {
    events: 0,
    sequence: 0,
  };

  let authTypes = filterGroups(
    accountUpdates.map((update) => {
      let json = update.toJSON();
      eventElements.events += update.body.events.data.length;
      eventElements.sequence += update.body.actions.data.length;
      return json.body.authorizationKind;
    })
  );
  /*
  np := proof
  n2 := signedPair
  n1 := signedSingle
  
  10.26*np + 10.08*n2 + 9.14*n1 < 69.45

  formula used to calculate how expensive a zkapp transaction is
  */

  let totalTimeRequired =
    proofCost * authTypes['proof'] +
    signedPairCost * authTypes['signedPair'] +
    signedSingleCost * authTypes['signedSingle'];

  let isWithinCostLimit = totalTimeRequired < costLimit;

  let isWithinEventsLimit = eventElements['events'] <= maxEventElements;
  let isWithinSequenceEventsLimit =
    eventElements['sequence'] <= maxSequenceEventElements;

  let error = '';

  if (!isWithinCostLimit) {
    // TODO: we should add a link to the docs explaining the reasoning behind it once we have such an explainer
    error += `Error: The transaction is too expensive, try reducing the number of AccountUpdates that are attached to the transaction.
Each transaction needs to be processed by the snark workers on the network.
Certain layouts of AccountUpdates require more proving time than others, and therefore are too expensive.

${JSON.stringify(authTypes)}
\n\n`;
  }

  if (!isWithinEventsLimit) {
    error += `Error: The AccountUpdates in your transaction are trying to emit too many events. The maximum allowed amount of events is ${maxEventElements}, but you tried to emit ${eventElements['events']}.\n\n`;
  }

  if (!isWithinSequenceEventsLimit) {
    error += `Error: The AccountUpdates in your transaction are trying to emit too many actions. The maximum allowed amount of actions is ${maxSequenceEventElements}, but you tried to emit ${eventElements['sequence']}.\n\n`;
  }

  if (error) throw Error('Error during transaction sending:\n\n' + error);
}

let S = 'Signature';
let N = 'None_given';
let P = 'Proof';

const isPair = (pair: string) =>
  pair == S + N || pair == N + S || pair == S + S || pair == N + N;

function filterPairs(xs: string[]): {
  xs: string[];
  pairs: number;
} {
  if (xs.length <= 1)
    return {
      xs,
      pairs: 0,
    };
  if (isPair(xs[0].concat(xs[1]))) {
    let rec = filterPairs(xs.slice(2));
    return {
      xs: rec.xs,
      pairs: rec.pairs + 1,
    };
  } else {
    let rec = filterPairs(xs.slice(1));
    return {
      xs: [xs[0]].concat(rec.xs),
      pairs: rec.pairs,
    };
  }
}

function filterGroups(xs: string[]) {
  let pairs = filterPairs(xs);
  xs = pairs.xs;

  let singleCount = 0;
  let proofCount = 0;

  xs.forEach((t) => {
    if (t == P) proofCount++;
    else singleCount++;
  });

  return {
    signedPair: pairs.pairs,
    signedSingle: singleCount,
    proof: proofCount,
  };
}
