import { Poseidon } from './hash';
import { Field } from './core'

export type Witness = {
  isLeft: boolean;
  sibling: Field;
}

export class MerkleTree {
  private nodes: Record<number, Record<string, Field>> = {};
  private zeroes: Field[];

  constructor(public readonly height: number) {
    this.zeroes = [Field(0)];
    for (let i = 1; i < height; i++) {
      this.zeroes.push(Poseidon.hash([this.zeroes[i - 1], this.zeroes[i - 1]]));
    }
  }

  getNode(level: number, index: bigint): Field {
    return this.nodes[level]?.[index.toString()] ?? this.zeroes[level];
  }

  getRoot(): Field {
    return this.getNode(this.height - 1, 0n);
  }
  
  private setNode(level: number, index: bigint, value: Field) {
    (this.nodes[level] ??= {})[index.toString()] = value;
  }

  setLeaf(index: bigint, leaf: Field) {
    this.setNode(0, index, leaf);
    let currIndex = index;
    for (let level = 1; level < this.height; level++) {
      currIndex = currIndex / 2n;

      const left = this.getNode(level - 1, currIndex * 2n);
      const right = this.getNode(level - 1, currIndex * 2n + 1n);

      this.setNode(level, currIndex, Poseidon.hash([left, right]));
    }
  }
}
