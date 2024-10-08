import { Field, Bool } from '../wrapped.js';
import { Struct } from '../types/struct.js';
import { MerkleTree, BaseMerkleWitness, MerkleWitness } from '../merkle-tree.js';
import { Proof, SelfProof, ZkProgram } from '../../proof-system/zkprogram.js';
import { Provable } from '../provable.js';
import { constraintSystem, print } from '../../testing/constraint-system.js';                                                                                                                             import { field, bigintField } from '../../testing/equivalent.js';
import { Poseidon } from '../crypto/poseidon.js';
import { expect } from 'expect';
import { describe, it } from 'node:test';

// Rewriting the [BaseMerkleWitness] API in a provable manner

function conditionalSwap(b: Bool, x: Field, y: Field): [Field, Field] {
  let m = b.toField().mul(x.sub(y)); // b*(x - y)
  const x_ = y.add(m); // y + b*(x - y)
  const y_ = x.sub(m); // x - b*(x - y) = x + b*(y - x)
  return [x_, y_];
}

const MAX_HEIGHT = 32;

class ProvableMerkleWitness extends Struct({
  height: Number,
  path: Provable.Array(Field, MAX_HEIGHT - 1),
  isLeft: Provable.Array(Bool, MAX_HEIGHT - 1)
}) {
  static from(witness: BaseMerkleWitness) {
    const n = witness.height();
    return new ProvableMerkleWitness({
      height: n,
      path: Array.from({ length: MAX_HEIGHT - 1 }, (i: number, _) => (i + 1 < n ? witness.path[i] : Field(0n))),
      isLeft: Array.from({ length: MAX_HEIGHT - 1 }, (i: number, _) => (i + 1 < n ? witness.isLeft[i] : Bool(false)))
    });
  }

  calculateRoot(leaf: Field): Field {
    const n = this.height;
    let hash = leaf;                                                                                                                                                                                      

    for (let i = 1; i < n; ++i) {
      let isLeft: Bool = this.isLeft[i - 1];
      const [left, right] = conditionalSwap(isLeft, hash, this.path[i - 1]);
      hash = Poseidon.hash([left, right]);
    }

    return hash;
  }

  calculateIndex(): Field {
    const n = this.height;
    let powerOfTwo = Field(1);
    let index = Field(0);

    for (let i = 1; i < n; ++i) {
      index = Provable.if(this.isLeft[i - 1], index, index.add(powerOfTwo));
      powerOfTwo = powerOfTwo.mul(2);
    }

    return index;
  }
}

//ZkProgram as a verifier for stateful Merkle-tree
let statefulMerkleTreeVerifier = ZkProgram({
  name: 'stateful-merkle-tree-verifier',
  publicOutput: Field,
  methods: {
    selfVerify: {
      privateInputs: [SelfProof],
      async method(proof: SelfProof<void, Field>) {
        proof.verify();
        return proof.publicOutput;
      }
    },
    unmodifiedMerklePathVerify: {
      privateInputs: [Field, Field, Field, ProvableMerkleWitness],
      async method(idx: Field, leafValue: Field, root: Field, witness: ProvableMerkleWitness) {
        witness.calculateIndex().assertEquals(idx);
        witness.calculateRoot(leafValue).assertEquals(root);
        return root;
      }
    },
    modifiedMerklePathVerify: {
      privateInputs: [Field, Field, Field, Field, ProvableMerkleWitness],
      async method(idx: Field, updatedValue: Field, previousValue: Field, previousRoot: Field, witness: ProvableMerkleWitness) {
        witness.calculateIndex().assertEquals(idx);
        witness.calculateRoot(previousValue).assertEquals(previousRoot);
        return witness.calculateRoot(updatedValue);
      }
    },
    recursiveUnmodifiedMerklePathVerify: {
      privateInputs: [Field, Field, ProvableMerkleWitness, SelfProof],
      async method(idx: Field, leafValue: Field, witness: ProvableMerkleWitness, previousProof: SelfProof<void, Field>) {
        previousProof.verify();
        witness.calculateIndex().assertEquals(idx);
        const root = previousProof.publicOutput;
        witness.calculateRoot(leafValue).assertEquals(root);
        return root;
      }
    },
    recursiveModifiedMerklePathVerify: {
      privateInputs: [Field, Field, Field, ProvableMerkleWitness, SelfProof],
      async method(idx: Field, updatedValue: Field, previousValue: Field, witness: ProvableMerkleWitness, previousProof: SelfProof<void, Field>) {
        previousProof.verify();
        witness.calculateIndex().assertEquals(idx);
        witness.calculateRoot(previousValue).assertEquals(previousProof.publicOutput);
        return witness.calculateRoot(updatedValue);
      }
    }
  }
});

// Stateful Merkle-tree API
class StatefulMerkleTree {
  tree: MerkleTree;
  stateProof: Proof<void, Field>;
  leafCount: bigint;
  PathWitness: typeof BaseMerkleWitness;

  constructor(readonly height: number) {
    expect(height).toBeGreaterThan(0);
    this.tree = new MerkleTree(height);
    this.leafCount = this.tree.leafCount;
    this.PathWitness = MerkleWitness(height);
  }

  async access(idx: bigint) {
    expect(idx).toBeGreaterThanOrEqual(0);
    expect(idx).toBeLessThan(this.leafCount);
    const val = this.tree.getLeaf(idx);
    const merklePathWitness = ProvableMerkleWitness.from(new this.PathWitness(this.tree.getWitness(idx)));
    if (this.stateProof && this.stateProof.shouldVerify.toBoolean())
      this.stateProof = await statefulMerkleTreeVerifier.recursiveUnmodifiedMerklePathVerify(Field(idx), val, merklePathWitness, this.stateProof);
    else
      this.stateProof = await statefulMerkleTreeVerifier.unmodifiedMerklePathVerify(Field(idx), val, this.tree.getRoot(), merklePathWitness);
    return val;
  }

  async update(idx: bigint, newVal: Field) {
    expect(idx).toBeGreaterThanOrEqual(0);
    expect(idx).toBeLessThan(this.leafCount);
    const val = this.tree.getLeaf(idx);
    const merklePathWitness = ProvableMerkleWitness.from(new this.PathWitness(this.tree.getWitness(idx)));
    if (this.stateProof && this.stateProof.shouldVerify.toBoolean())
      this.stateProof = await statefulMerkleTreeVerifier.recursiveModifiedMerklePathVerify(Field(idx), newVal, val, merklePathWitness, this.stateProof);
    else
      this.stateProof = await statefulMerkleTreeVerifier.modifiedMerklePathVerify(Field(idx), newVal, val, this.tree.getRoot(), merklePathWitness);
    this.tree.setLeaf(idx, newVal);
  }

  async selfVerify() {
    if (this.stateProof && this.stateProof.shouldVerify.toBoolean())
      this.stateProof = await statefulMerkleTreeVerifier.selfVerify(this.stateProof);
  }
}

// -----------------Tests and benchmarks------------------

// building constraint systems, failed with runtime or verification error

console.log('sizeInFields' in SelfProof);

constraintSystem.fromZkProgram(
  statefulMerkleTreeVerifier,
  //'selfVerify',
  'unmodifiedMerklePathVerify',
  //'modifiedMerklePathVerify',
  //'recursiveUnmodifiedMerklePathVerify',
  //'recursiveModifiedMerklePathVerify',
  print
);


// This is not the correct usage of bigintField, but where is the referrence to the correct usage?
/*
const stMKT = new StatefulMerkleTree(MAX_HEIGHT);

console.log(
  constraintSystem.size({
    from: [field]
  },
  (idx) => {
    stMKT.access(Provable.toConstant(bigintField, idx));
  })
);
*/

// Ridiculous analysis result of the circuits...
console.time('Stateful Merkle-tree verifier: compile');
await statefulMerkleTreeVerifier.compile();
console.timeEnd('Stateful Merkle-tree verifier: compile');

{
    console.time('Stateful Merkle-tree verifier: building contraint system - selfVerify');
    let cs = (await statefulMerkleTreeVerifier.analyzeMethods()).selfVerify;
    console.timeEnd('Stateful Merkle-tree verifier: building contraint system - selfVerify');
    console.log(cs.summary());
}

{
    console.time('Stateful Merkle-tree verifier: building contraint system - unmodifiedMerklePathVerify');
    let cs = (await statefulMerkleTreeVerifier.analyzeMethods()).unmodifiedMerklePathVerify;
    console.timeEnd('Stateful Merkle-tree verifier: building contraint system - unmodifiedMerklePathVerify');
    console.log(cs.summary());
}

{
    console.time('Stateful Merkle-tree verifier: building contraint system - modifiedMerklePathVerify');
    let cs = (await statefulMerkleTreeVerifier.analyzeMethods()).modifiedMerklePathVerify;
    console.timeEnd('Stateful Merkle-tree verifier: building contraint system - modifiedMerklePathVerify');
    console.log(cs.summary());
}

{
    console.time('Stateful Merkle-tree verifier: building contraint system - recursiveUnmodifiedMerklePathVerify');
    let cs = (await statefulMerkleTreeVerifier.analyzeMethods()).recursiveUnmodifiedMerklePathVerify;
    console.timeEnd('Stateful Merkle-tree verifier: building contraint system - recursiveUnmodifiedMerklePathVerify');
    console.log(cs.summary());
}

{
    console.time('Stateful Merkle-tree verifier: building contraint system - recursiveModifiedMerklePathVerify');
    let cs = (await statefulMerkleTreeVerifier.analyzeMethods()).recursiveModifiedMerklePathVerify;
    console.timeEnd('Stateful Merkle-tree verifier: building contraint system - recursiveModifiedMerklePathVerify');
    console.log(cs.summary());
}

// Finally, the tests failed because of unknown internal circuit issues...
/*
describe('Stateful Merkle-tree action', async () => {
  it('Initial empty tree', async () => {
    const stMKT1 = new StatefulMerkleTree(1);
    expect(stMKT1.leafCount.toString()).toEqual('1');
    expect(stMKT1.stateProof).toBe(undefined);
  });

  it('Insert to tree of height 2', async () => {
    const stMKT2 = new StatefulMerkleTree(2);
    await stMKT2.update(0n, Field(1));
    await stMKT2.update(1n, Field(2));
    expect(stMKT2.stateProof.shouldVerify.toBoolean()).toBe(true);
    expect(stMKT2.stateProof.publicOutput.toString()).toEqual(
      Poseidon.hash([Field(1), Field(2)]).toString()
    );
  });

  it('Insert, update and access values', async () => {
    const stMKT3 = new StatefulMerkleTree(3);
    await stMKT3.update(1n, Field(32767));
    await stMKT3.update(2n, Field(1));
    //expect(stMKT3.access(1n).toString()).toEqual(Field(32767).toString());
    expect(stMKT3.access(1n).toString()).toEqual('32767');
    await stMKT3.update(2n, Field(64));
    //expect(stMKT3.access(1n).toString()).toEqual(Field(32767).toString());
    expect(stMKT3.access(1n).toString()).toEqual('32767');
    //expect(stMKT3.access(2n).toString()).toEqual(Field(64).toString());
    expect(stMKT3.access(2n).toString()).toEqual('64');
  });
  
  it('State proof self-verification', async () => {
    const stMKT2 = new StatefulMerkleTree(2);
    await stMKT2.update(0n, Field(1));
    expect(stMKT2.stateProof.shouldVerify.toBoolean()).toBe(true);
    stMKT2.selfVerify();
  });
});
*/

