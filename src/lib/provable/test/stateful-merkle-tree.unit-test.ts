import { MerkleTreeAsDatabase, MerkleTreeQueryAuth, MerkleTreeModifyAuth, MAX_TREE_HEIGHT } from '../merkle-tree-as-database.js';
import { MerkleTreeStateTransition, StatefulMerkleTreeController } from '../stateful-merkle-tree.js';
import { Field } from '../wrapped.js';
import { ZkProgram } from '../../proof-system/zkprogram.js';
import { Provable } from '../provable.js';
import { cryptoRandomStringAsync } from 'crypto-random-string';
import { expect } from 'expect';

// -----------------Tests and benchmarks------------------

// MKT as database operation simulation
async function randomMKTOps(height: number, opN: number) {
  let mkt = new MerkleTreeAsDatabase(height);
  const idxRange: bigint = mkt.leafCount;

  for (let i=0; i < opN; ++i) {
    const _idx: bigint = BigInt('0x' + await cryptoRandomStringAsync({ length: MAX_TREE_HEIGHT })) % idxRange;
    if (Math.random() < 0.5) {
      mkt.query(_idx);
    } else {
      const _newVal = Field(BigInt('0x' + await cryptoRandomStringAsync({ length: MAX_TREE_HEIGHT })));
      mkt.modify(_idx, _newVal);
    }
  }
}

{
  console.time('MKT-as-database initialization: height 2');
  await randomMKTOps(2, 0);
  console.timeEnd('MKT-as-database initialization: height 2');
}

{
  console.time('MKT-as-database operations: height 2, number of ops 10');
  await randomMKTOps(2, 10);
  console.timeEnd('MKT-as-database operations: height 2, number of ops 10');
}

{
  console.time('MKT-as-database initialization: height 20');
  await randomMKTOps(20, 0);
  console.timeEnd('MKT-as-database initialization: height 20');
}

{
  console.time('MKT-as-database operations: height 20, number of ops 1000');
  await randomMKTOps(20, 1000);
  console.timeEnd('MKT-as-database operations: height 20, number of ops 1000');
}

// Stateful MKT transition ZkProgram circuit information
// TODO: unable to load the correct circuit metadata
await MerkleTreeStateTransition.compile();

const methodsMeta = await MerkleTreeStateTransition.analyzeMethods();
expect(methodsMeta).toHaveProperty("modifyTransition");
expect(methodsMeta).toHaveProperty("queryTransition");
console.log(methodsMeta["modifyTransition"].print());
//console.log(methodsMeta["modifyTransition"].summary());
console.log(methodsMeta["queryTransition"].print());
//console.log(methodsMeta["queryTransition"].summary());

// Instantial tests and benchmarks
// TODO: ZkProgram methods fail when running, with internal errors of the circuit
{
  console.log("Instantial tests and benchmarks...");
  
  let mkt20 = new MerkleTreeAsDatabase(20);
  const empty20Root: Field = mkt20.root;

  let mkt20Controller = new StatefulMerkleTreeController(20);
  mkt20Controller.rootAsState.assertEquals(empty20Root);
  const proofOfStep1 = await mkt20Controller.modify(BigInt(164n), Field(2n)); // Proof seems not well formed, error message: 'the permutation was not constructed correctly: final value'
  //console.log(proofOfStep1);
  const proofOfStep2 = await mkt20Controller.query(BigInt(163n));
  //console.log(proofOfStep2);
  const proofOfStep3 = await mkt20Controller.query(BigInt(164n));
  //console.log(proofOfStep3);
  const proofOfStep4 = await mkt20Controller.modify(BigInt(396505n), Field(2n));
  //console.log(proofOfStep4);
  const proofOfStep5 = await mkt20Controller.query(BigInt(164n));
  //console.log(proofOfStep5);
}

