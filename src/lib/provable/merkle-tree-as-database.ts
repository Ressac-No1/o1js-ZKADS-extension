import { Provable } from './provable.js';
import { MerkleTree, Witness as MerklePathAuth } from './merkle-tree.js';
import { Field } from './wrapped.js';

export { MerkleTreeAsDatabase, MerkleTreeQueryAuth, MerkleTreeModifyAuth, MAX_TREE_HEIGHT };

const MAX_TREE_HEIGHT = 31;

type MerkleTreeQueryAuth = {
  height: number;
  idx: bigint;
  val: Field;
  isLeft: boolean[];
  sibling: Field[];
};

type MerkleTreeModifyAuth = {
  height: number;
  idx: bigint;
  val: Field;
  newVal: Field;
  isLeft: boolean[];
  sibling: Field[];
}

class MerkleTreeAsDatabase {
  #tree: MerkleTree;
  #height: number;
  #leafCount: bigint;
  root: Field;

  constructor(readonly height: number) {
    if (height > 1 && height <= MAX_TREE_HEIGHT) {
      this.#tree = new MerkleTree(height);
      this.#height = height;
      this.#leafCount = this.#tree.leafCount;
      this.root = this.#tree.getRoot();
    } else {
      this.#height = 0;
      this.#leafCount = BigInt(0);
      this.root = Field(0);
      throw new Error(`Tree height must be an interger within [1..${MAX_TREE_HEIGHT}]`);
    }
  }
  
  get leafCount(): bigint {
    return this.#leafCount;
  }

  query(_idx: bigint): MerkleTreeQueryAuth {
    if (_idx >= 0 && _idx < this.#leafCount) {
      const value = this.#tree.getLeaf(_idx);
      const pathAuth: MerklePathAuth = this.#tree.getWitness(_idx);
      return {
        height: this.#height,
        idx: _idx,
        val: value,
        isLeft: pathAuth.map((_) => _.isLeft),
        sibling: pathAuth.map((_) => _.sibling)
      };
    } else
      throw new Error(`Leaf index ${_idx} is out of range for ${this.#leafCount} leaves.`);
  }
  
  modify(_idx: bigint, _newVal: Field): MerkleTreeModifyAuth {
    if (_idx >= 0 && _idx < this.#leafCount) {
      const value = this.#tree.getLeaf(_idx);
      const pathAuth: MerklePathAuth = this.#tree.getWitness(_idx);
      this.#tree.setLeaf(_idx, _newVal);
      this.root = this.#tree.getRoot();
      return {
        height: this.#height,
        idx: _idx,
        val: value,
        newVal: _newVal,
        isLeft: pathAuth.map((_) => _.isLeft),
        sibling: pathAuth.map((_) => _.sibling)
      };
    } else
      throw new Error(`Leaf index ${_idx} is out of range for ${this.#leafCount} leaves.`);
  }
}

