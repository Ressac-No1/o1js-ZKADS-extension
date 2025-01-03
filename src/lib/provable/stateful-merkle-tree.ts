import { Provable } from './provable.js';
import { MerkleTreeAsDatabase, MerkleTreeQueryAuth, MerkleTreeModifyAuth, MAX_TREE_HEIGHT } from './merkle-tree-as-database.js';
import { Field, Bool } from './wrapped.js';
import { Struct } from './types/struct.js';
import { ZkProgram } from '../proof-system/zkprogram.js';
import { Poseidon } from './crypto/poseidon.js';

export { MerklePathAuthAsWitness, MerkleTreeStateTransition, StatefulMerkleTreeController };

function conditionalSwap(b: Bool, x: Field, y: Field): [Field, Field] {
  let m = b.toField().mul(x.sub(y));
  const x_ = y.add(m);
  const y_ = x.sub(m);
  return [x_, y_];
}

class MerklePathAuthAsWitness extends Struct({
  height: Number,
  isLeft: Provable.Array(Bool, MAX_TREE_HEIGHT - 1),
  siblingHash: Provable.Array(Field, MAX_TREE_HEIGHT - 1),
}) {
  calculateRoot(leafValue: Field): Field {
    const n = this.height;
    let hash = leafValue;
    for (let i=1; i < n; ++i) {
      const [left, right] = conditionalSwap(this.isLeft[i - 1], hash, this.siblingHash[i - 1]);
      hash = Poseidon.hash([left, right]);
    }
    return hash;
  }
 
  calculateIndex(): Field {
    const n = this.height;
    let powerOfTwo = Field(1);
    let index = Field(0);
    for (let i=1; i < n; ++i) {
      index = Provable.if(this.isLeft[i - 1], index, index.add(powerOfTwo));
      powerOfTwo = powerOfTwo.mul(2);
    }
    return index;
  }
}

let MerkleTreeStateTransition = ZkProgram({
  name: 'merkle-tree-state-transition',
  publicInput: Field,
  publicOutput: Field,
  methods: {
    queryTransition: {
      privateInputs: [Field, Field, MerklePathAuthAsWitness],
      async method(publicInput: Field, idx: Field, value: Field, merklePathAuth: MerklePathAuthAsWitness) {
        merklePathAuth.calculateIndex().assertEquals(idx);
        const root = merklePathAuth.calculateRoot(value);
        publicInput.assertEquals(root);
        return { publicOutput: root };
      }
    },
    modifyTransition: {
      privateInputs: [Field, Field, Field, MerklePathAuthAsWitness],
      async method(publicInput: Field, idx: Field, previousValue: Field, newValue: Field, merklePathAuth: MerklePathAuthAsWitness) {
        merklePathAuth.calculateIndex().assertEquals(idx);
        const previousRoot = merklePathAuth.calculateRoot(previousValue);
        publicInput.assertEquals(previousRoot);
        return { publicOutput: merklePathAuth.calculateRoot(newValue) };
      }
    }
  }
});

class StatefulMerkleTreeController {
  merkleDB: MerkleTreeAsDatabase;
  rootAsState: Field;

  constructor(readonly height: number) {
    try {
      this.merkleDB = new MerkleTreeAsDatabase(height);
      this.rootAsState = this.merkleDB.root;
    } catch (error) {
      console.log(error);
    }
  }

  async query(idx: bigint) {
    try {
      const auth: MerkleTreeQueryAuth = this.merkleDB.query(idx);
      const idxAsWitness = Provable.witness(Field, () => idx);
      const merklePathAuth = Provable.witness(MerklePathAuthAsWitness, () => {
        return new MerklePathAuthAsWitness({
          height: auth.height,
          isLeft: Array.from({ length: MAX_TREE_HEIGHT - 1 }, (_, i: number) => (i + 1 < auth.height ? Bool(auth.isLeft[i]) : Bool(true))),
          siblingHash: Array.from({ length: MAX_TREE_HEIGHT - 1 }, (_, i: number) => (i + 1 < auth.height ? auth.sibling[i] : Field(0)))
        });
      });

      const proof = (await MerkleTreeStateTransition.queryTransition(this.rootAsState, idxAsWitness, auth.val, merklePathAuth)).proof;
      this.rootAsState = proof.publicOutput;
      return proof;
    } catch (error) {
      console.log(error);
    }
  }
  
  async modify(idx: bigint, newVal: Field) {
    try {
      const auth: MerkleTreeModifyAuth = this.merkleDB.modify(idx, newVal);
      const idxAsWitness = Provable.witness(Field, () => idx);
      const merklePathAuth = Provable.witness(MerklePathAuthAsWitness, () => {
        return new MerklePathAuthAsWitness({
          height: auth.height,
          isLeft: Array.from({ length: MAX_TREE_HEIGHT - 1 }, (_, i: number) => (i + 1 < auth.height ? Bool(auth.isLeft[i]) : Bool(true))),
          siblingHash: Array.from({ length: MAX_TREE_HEIGHT - 1 }, (_, i: number) => (i + 1 < auth.height ? auth.sibling[i] : Field(0)))
        });
      });

      const proof = (await MerkleTreeStateTransition.modifyTransition(this.rootAsState, idxAsWitness, auth.val, auth.newVal, merklePathAuth)).proof;
      this.rootAsState = proof.publicOutput;
      return proof;
    } catch (error) {
      console.log(error);
    }  
  }
}
