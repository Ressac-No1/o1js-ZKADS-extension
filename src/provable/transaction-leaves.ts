import { Field, Bool } from '../lib/core.js';
import { UInt32, UInt64, Sign } from '../lib/int.js';
import { PublicKey } from '../lib/signature.js';
import { derivedLeafTypes } from './derived-leaves.js';
import { createEvents, dataAsHash } from '../lib/events.js';
import { Poseidon } from '../lib/hash.js';
import { provable } from '../lib/circuit_value.js';

export {
  PublicKey,
  Field,
  Bool,
  AuthRequired,
  AuthorizationKind,
  UInt64,
  UInt32,
  Sign,
  TokenId,
};

export { Events, SequenceEvents, StringWithHash, TokenSymbol, SequenceState };

type AuthRequired = {
  constant: Bool;
  signatureNecessary: Bool;
  signatureSufficient: Bool;
};
type AuthorizationKind = { isSigned: Bool; isProved: Bool };
type TokenId = Field;
type TokenSymbol = { symbol: string; field: Field };

const { TokenId, TokenSymbol, AuthRequired, AuthorizationKind } =
  derivedLeafTypes({ Field, Bool });

// types which got an annotation about its circuit type in Ocaml

type Event = Field[];
type Events = {
  hash: Field;
  data: Event[];
};
type SequenceEvents = Events;
const { Events, SequenceEvents } = createEvents({ Field, Poseidon });

type SequenceState = Field;
const SequenceState = {
  ...provable(Field),
  emptyValue: SequenceEvents.emptySequenceState,
};

const StringWithHash = dataAsHash<string, string, Field>({
  emptyValue() {
    return {
      data: '',
      hash: Field(
        '22930868938364086394602058221028773520482901241511717002947639863679740444066'
      ),
    };
  },
  toJSON(data: string) {
    return data;
  },
  fromJSON(json: string) {
    let data = json;
    // TODO compute hash
    throw Error('unimplemented');
  },
});
