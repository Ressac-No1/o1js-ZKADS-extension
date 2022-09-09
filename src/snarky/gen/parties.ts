// @generated this file is auto-generated - don't edit it directly

import {
  PublicKey,
  UInt64,
  UInt32,
  TokenId,
  Field,
  Bool,
  AuthRequired,
  TokenSymbol,
  Sign,
  StringWithHash,
  Events,
  SequenceEvents,
} from '../parties-leaves.js';
import { asFieldsAndAux, AsFieldsAndAux } from '../parties-helpers.js';
import * as Json from './parties-json.js';
import { jsLayout } from './js-layout.js';

export { customTypes, Parties, Party };
export { Json };
export * from '../parties-leaves.js';

type CustomTypes = {
  StringWithHash: AsFieldsAndAux<
    {
      data: string;
      hash: Field;
    },
    Json.TypeMap['string']
  >;
  TokenSymbol: AsFieldsAndAux<TokenSymbol, Json.TypeMap['string']>;
  Events: AsFieldsAndAux<
    {
      data: Field[][];
      hash: Field;
    },
    Json.TypeMap['Field'][][]
  >;
  SequenceEvents: AsFieldsAndAux<
    {
      data: Field[][];
      hash: Field;
    },
    Json.TypeMap['Field'][][]
  >;
};
let customTypes: CustomTypes = {
  StringWithHash,
  TokenSymbol,
  Events,
  SequenceEvents,
};

type Parties = {
  feePayer: {
    body: {
      publicKey: PublicKey;
      fee: UInt64;
      validUntil?: UInt32;
      nonce: UInt32;
    };
    authorization: {
      proof?: string;
      signature?: string;
    };
  };
  otherParties: {
    body: {
      publicKey: PublicKey;
      tokenId: TokenId;
      update: {
        appState: { isSome: Bool; value: Field }[];
        delegate: { isSome: Bool; value: PublicKey };
        verificationKey: {
          isSome: Bool;
          value: {
            data: string;
            hash: Field;
          };
        };
        permissions: {
          isSome: Bool;
          value: {
            editState: AuthRequired;
            send: AuthRequired;
            receive: AuthRequired;
            setDelegate: AuthRequired;
            setPermissions: AuthRequired;
            setVerificationKey: AuthRequired;
            setZkappUri: AuthRequired;
            editSequenceState: AuthRequired;
            setTokenSymbol: AuthRequired;
            incrementNonce: AuthRequired;
            setVotingFor: AuthRequired;
          };
        };
        zkappUri: {
          isSome: Bool;
          value: {
            data: string;
            hash: Field;
          };
        };
        tokenSymbol: { isSome: Bool; value: TokenSymbol };
        timing: {
          isSome: Bool;
          value: {
            initialMinimumBalance: UInt64;
            cliffTime: UInt32;
            cliffAmount: UInt64;
            vestingPeriod: UInt32;
            vestingIncrement: UInt64;
          };
        };
        votingFor: { isSome: Bool; value: Field };
      };
      balanceChange: {
        magnitude: UInt64;
        sgn: Sign;
      };
      incrementNonce: Bool;
      events: {
        data: Field[][];
        hash: Field;
      };
      sequenceEvents: {
        data: Field[][];
        hash: Field;
      };
      callData: Field;
      callDepth: number;
      preconditions: {
        network: {
          snarkedLedgerHash: { isSome: Bool; value: Field };
          timestamp: {
            isSome: Bool;
            value: {
              lower: UInt64;
              upper: UInt64;
            };
          };
          blockchainLength: {
            isSome: Bool;
            value: {
              lower: UInt32;
              upper: UInt32;
            };
          };
          minWindowDensity: {
            isSome: Bool;
            value: {
              lower: UInt32;
              upper: UInt32;
            };
          };
          totalCurrency: {
            isSome: Bool;
            value: {
              lower: UInt64;
              upper: UInt64;
            };
          };
          globalSlotSinceHardFork: {
            isSome: Bool;
            value: {
              lower: UInt32;
              upper: UInt32;
            };
          };
          globalSlotSinceGenesis: {
            isSome: Bool;
            value: {
              lower: UInt32;
              upper: UInt32;
            };
          };
          stakingEpochData: {
            ledger: {
              hash: { isSome: Bool; value: Field };
              totalCurrency: {
                isSome: Bool;
                value: {
                  lower: UInt64;
                  upper: UInt64;
                };
              };
            };
            seed: { isSome: Bool; value: Field };
            startCheckpoint: { isSome: Bool; value: Field };
            lockCheckpoint: { isSome: Bool; value: Field };
            epochLength: {
              isSome: Bool;
              value: {
                lower: UInt32;
                upper: UInt32;
              };
            };
          };
          nextEpochData: {
            ledger: {
              hash: { isSome: Bool; value: Field };
              totalCurrency: {
                isSome: Bool;
                value: {
                  lower: UInt64;
                  upper: UInt64;
                };
              };
            };
            seed: { isSome: Bool; value: Field };
            startCheckpoint: { isSome: Bool; value: Field };
            lockCheckpoint: { isSome: Bool; value: Field };
            epochLength: {
              isSome: Bool;
              value: {
                lower: UInt32;
                upper: UInt32;
              };
            };
          };
        };
        account: {
          balance: {
            isSome: Bool;
            value: {
              lower: UInt64;
              upper: UInt64;
            };
          };
          nonce: {
            isSome: Bool;
            value: {
              lower: UInt32;
              upper: UInt32;
            };
          };
          receiptChainHash: { isSome: Bool; value: Field };
          delegate: { isSome: Bool; value: PublicKey };
          state: { isSome: Bool; value: Field }[];
          sequenceState: { isSome: Bool; value: Field };
          provedState: { isSome: Bool; value: Bool };
          isNew: { isSome: Bool; value: Bool };
        };
      };
      useFullCommitment: Bool;
      caller: TokenId;
    };
    authorization: {
      proof?: string;
      signature?: string;
    };
  }[];
  memo: string;
};

let Parties = asFieldsAndAux<Parties, Json.Parties>(
  jsLayout.Parties as any,
  customTypes
);

type Party = {
  body: {
    publicKey: PublicKey;
    tokenId: TokenId;
    update: {
      appState: { isSome: Bool; value: Field }[];
      delegate: { isSome: Bool; value: PublicKey };
      verificationKey: {
        isSome: Bool;
        value: {
          data: string;
          hash: Field;
        };
      };
      permissions: {
        isSome: Bool;
        value: {
          editState: AuthRequired;
          send: AuthRequired;
          receive: AuthRequired;
          setDelegate: AuthRequired;
          setPermissions: AuthRequired;
          setVerificationKey: AuthRequired;
          setZkappUri: AuthRequired;
          editSequenceState: AuthRequired;
          setTokenSymbol: AuthRequired;
          incrementNonce: AuthRequired;
          setVotingFor: AuthRequired;
        };
      };
      zkappUri: {
        isSome: Bool;
        value: {
          data: string;
          hash: Field;
        };
      };
      tokenSymbol: { isSome: Bool; value: TokenSymbol };
      timing: {
        isSome: Bool;
        value: {
          initialMinimumBalance: UInt64;
          cliffTime: UInt32;
          cliffAmount: UInt64;
          vestingPeriod: UInt32;
          vestingIncrement: UInt64;
        };
      };
      votingFor: { isSome: Bool; value: Field };
    };
    balanceChange: {
      magnitude: UInt64;
      sgn: Sign;
    };
    incrementNonce: Bool;
    events: {
      data: Field[][];
      hash: Field;
    };
    sequenceEvents: {
      data: Field[][];
      hash: Field;
    };
    callData: Field;
    callDepth: number;
    preconditions: {
      network: {
        snarkedLedgerHash: { isSome: Bool; value: Field };
        timestamp: {
          isSome: Bool;
          value: {
            lower: UInt64;
            upper: UInt64;
          };
        };
        blockchainLength: {
          isSome: Bool;
          value: {
            lower: UInt32;
            upper: UInt32;
          };
        };
        minWindowDensity: {
          isSome: Bool;
          value: {
            lower: UInt32;
            upper: UInt32;
          };
        };
        totalCurrency: {
          isSome: Bool;
          value: {
            lower: UInt64;
            upper: UInt64;
          };
        };
        globalSlotSinceHardFork: {
          isSome: Bool;
          value: {
            lower: UInt32;
            upper: UInt32;
          };
        };
        globalSlotSinceGenesis: {
          isSome: Bool;
          value: {
            lower: UInt32;
            upper: UInt32;
          };
        };
        stakingEpochData: {
          ledger: {
            hash: { isSome: Bool; value: Field };
            totalCurrency: {
              isSome: Bool;
              value: {
                lower: UInt64;
                upper: UInt64;
              };
            };
          };
          seed: { isSome: Bool; value: Field };
          startCheckpoint: { isSome: Bool; value: Field };
          lockCheckpoint: { isSome: Bool; value: Field };
          epochLength: {
            isSome: Bool;
            value: {
              lower: UInt32;
              upper: UInt32;
            };
          };
        };
        nextEpochData: {
          ledger: {
            hash: { isSome: Bool; value: Field };
            totalCurrency: {
              isSome: Bool;
              value: {
                lower: UInt64;
                upper: UInt64;
              };
            };
          };
          seed: { isSome: Bool; value: Field };
          startCheckpoint: { isSome: Bool; value: Field };
          lockCheckpoint: { isSome: Bool; value: Field };
          epochLength: {
            isSome: Bool;
            value: {
              lower: UInt32;
              upper: UInt32;
            };
          };
        };
      };
      account: {
        balance: {
          isSome: Bool;
          value: {
            lower: UInt64;
            upper: UInt64;
          };
        };
        nonce: {
          isSome: Bool;
          value: {
            lower: UInt32;
            upper: UInt32;
          };
        };
        receiptChainHash: { isSome: Bool; value: Field };
        delegate: { isSome: Bool; value: PublicKey };
        state: { isSome: Bool; value: Field }[];
        sequenceState: { isSome: Bool; value: Field };
        provedState: { isSome: Bool; value: Bool };
        isNew: { isSome: Bool; value: Bool };
      };
    };
    useFullCommitment: Bool;
    caller: TokenId;
  };
  authorization: {
    proof?: string;
    signature?: string;
  };
};

let Party = asFieldsAndAux<Party, Json.Party>(
  jsLayout.Party as any,
  customTypes
);
