## Stateful data struture extension R&D
Mina&o1js data storage scaling program that enables more advanced stateful authenticated data structure modules that support a wider range of data processing operations.

## Proposal Overview

### Problem
Mina's succinctness is ultimately determined by off-chain database processing. The chain stores nothing but verified zero-knowledge proofs, and all the data involved in a contract call are dropped offline with only a small amount (usually *O*(1)) of summarized values referred to for certain operation results on those data and ZK proofs of the correctness of such results. Currently, with o1js as Mina core, the sole supporting module for off-chain data processing is an authenticated Merkle tree. Although the Merkle tree can ensure data integrity and reliability for modification or query operation results with its root hash (*O*(1) size) and Merkle path proof (*O*(log *N*) size), its inherent limitation is that only one element stored as a Merkle leaf can be operated per modification or query operation. Solutions are urged to scale Mina's off-chain data storage system, and a straightforward approach is to build other authenticated data structures to organize off-chain data.

### Solution
This project targets the integration of zero-knowledge authenticated data structure modules into o1js. These modules manage off-chain user data and offer various modification, query, and statistical analysis operation interfaces for advanced data processing, along with relevant ZK proofs of operation execution available to the public. Specifically, the authenticated data structure modules render **statefulness** to guarantee the integrity of the whole database through visible state to the public, and each ZK proof confirms the transition of an old state to a new one resulting from single or batched data structure operations.

### Impact
- Upgrading the built-in data storage system of the o1js core to be used for massive data processing and statistical analysis in Mina development
- Boosting Mina ZK apps utilizing large-scale and advanced databases
- Initiating exploration of an enhanced Mina-like proof system that is compatible with existing widely used database management handles, e.g., SQL
- Inspiring further research into authenticated data structures and their contributions to lightweight on-chain ecosystems

### Audience
- Within Mina ecosystem: cryptographic protocol researchers, o1js core builders, and ZK app developers
- Universal: researchers and developers focusing on ZK-protected data structure models and ZK proof systems compatible with them


## Architecture & Design

### Detailed Design/Architecture
#### Stateful authenticated data structure as a database
![](https://github.com/Ressac-No1/o1js-ZKADS-extension/blob/feature/stateful-MKT-extension/presentations/Growth_Track/Growth_Proposal_Img_0.png?raw=true)
For each implemented authenticated data structure, it stores and organizes off-chain user data and interacts with user requests via customized operation handles. Each data structure module comprises three components, all of which are defined as *provable* in the o1js core.
- data structure as a database (DSaaD): where user data are eventually stored and processed once a user request is received. The database generates raw authentication metadata as the return value of each supported operation
- provability serializer: where the raw authentication metadata from the operations at DSaaD are collected and serialized into provable types to be used as witnesses of a ZK circuit
- ZkProgram as a state transition proof generator: where the ZK proof of operation execution is generated via a specific ZkProgram method, in which the previous state value acts as the public input, the provable serialized authentication metadata of the executed operation is the private inputs, and the update state value as the result of the operation is shown in the public output

#### Universal state controller
![](https://github.com/Ressac-No1/o1js-ZKADS-extension/blob/feature/stateful-MKT-extension/presentations/Growth_Track/Growth_Proposal_Img_1.png?raw=true)
Here, the global state values of all authenticated data structures deployed as databases are preserved, and the controller is also a general interface through which users can interact. The state values are open to the public whenever they are checked; thus, global state updating can be traced by recording its persistence and trusted by verifying the state transition proofs from the ZkProgram.

#### Tests and benchmarks
Unit tests and benchmarks of the implemented authenticated data structure modules are also included in the deployment of the o1js core upgrade. The proposed model evaluates the following measurements via complexity analyses and/or benchmarks:
- Circuit size in terms of constraints and witness size (complexity analyzable in most cases)
- State transition proof size
- Time and cost of operation execution in DSaaD (complexity analyzable in most cases)
- ZkProgram proving and verification time and cost

### Vision
This proposal outlines the initial stage of an o1js core extension plan, in which stateful authenticated data structure modules are entirely built within the given proof system of Mina protocol. Goals of further stages possibly encompass amendment to the Mina proof system to achieve better performance in massive data processing, which may yield a more specific ZK protocol to suit the authenticated data structures that drives Mina’s advancement.

### Existing Work
The preliminary work consists of the design and implementation of a stateful Merkle tree based on the existing Merkle tree module in o1js and formalized as the architecture described above. Note [the *stateful-MKT-extension* feature branch](https://github.com/Ressac-No1/o1js-ZKADS-extension/tree/feature/stateful-MKT-extension) of o1js.

### Production Timeline
The stateful authenticated data structure modules are ready in production once the theoretical design scheme is presented and all related components are deployed in the o1js core with all necessary unit tests passed. The estimated implementation time of the first authenticated data structure other than the Merkle tree is approximately 2 months since the project launch.


## Budget & milestones

### Deliverables
- Report of the theoretical design scheme of authenticated data structures applicable to o1js core extension, with complexity analysis
- Implementation of stateful authenticated data structures in the o1js core, including DSaaD, provability serializer, ZkProgram as a state transition proof generator, universal state controller, and relevant unit tests and benchmarks
- Documentation of usage, similar to the Merkle tree usage instruction in the official documentation of Mina protocol

### Mid-Point milestones
- Milestone 1 (5-7 weeks since start): Summarize existing solutions from publication, try to solve the issue of statistical result authentication in data structures, present detailed design schemes in a report
- Milestone 2 (11-12 weeks since start): Implement the modules in the o1js core with all related unit tests pass, analyze and summarize the benchmark results, deploy to the o1js repo on Github
- Milestone 3 (3 months since start, final target): Gather all results in the final report, update the documentation, including usage and sample contracts leveraging the authenticated data structure modules for off-chain data storage and processing

### Project Timeline
3 Months

### Budget Requested
30,000 MINA

### Budget Breakdown
- 15,000 MINA for research, theoretical design, and complexity analyses
- 10,000 MINA for implementation, tests and benchmarks on o1js
- 5,000 MINA for updating the documentation

### Wallet Address
B62qr4m8vjn5C1obEmMNNKoiwE6HrEWEuoBz49qYLsB3XHjcuD67PLy

## Team Info
This project will be completed by RSSCNo1 solely.
### Proposer Github
github.com/Ressac-No1

### Proposer Experience
I am a digital nomad focusing on the R&D of privacy-enhancing techniques applied to the Web3 industry, especially zero-knowledge-oriented protocols. I also keep my interest in some theoretical computer science topics, such as advanced data structures, thanks to my previous experience in algorithm programming contests.

### Team Members
- RSSCNo1 (github handle: Ressac-No1, Telegram: t.me/rsscno1)


## Risks & Mitigations
Currently, the majority of existing authenticated data structure design methods rely on collision-resistant hash functions, which typically lack computation homomorphism, thereby hindering their ability to authenticate statistical analysis results during database updates. Redesigning the framework of authenticated data structures necessitates conducting some research work to enable statistical results.

A significant challenge arises when developing state transition ZkProgram components, as the current o1js proof system lacks support for ROM access, resulting in provable arrays functioning as witnesses being limited to a fixed length. This hinders the adoption of certain data structures with amortized efficiency or authentication metadata attributes of dynamic length, which can only be resolved with tailored encoding and decoding protocols.

