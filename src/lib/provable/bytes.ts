import { provableFromClass } from './types/provable-derivers.js';
import type { ProvablePureExtended } from './types/struct.js';
import { assert } from './gadgets/common.js';
import { chunkString } from '../util/arrays.js';
import { Provable } from './provable.js';
import { UInt8 } from './int.js';
import { randomBytes } from '../../bindings/crypto/random.js';
import { Field } from './field.js';
import { Bool } from './bool.js';

// external API
export { Bytes };

// internal API
export { createBytes, FlexibleBytes };

type FlexibleBytes = Bytes | (UInt8 | bigint | number)[] | Uint8Array;

/**
 * A provable type representing an array of bytes.
 */
class Bytes {
  bytes: UInt8[];

  constructor(bytes: UInt8[]) {
    let size = (this.constructor as typeof Bytes).size;

    // assert that data is not too long
    assert(
      bytes.length <= size,
      `Expected at most ${size} bytes, got ${bytes.length}`
    );

    // pad the data with zeros
    let padding = Array.from(
      { length: size - bytes.length },
      () => new UInt8(0)
    );
    this.bytes = bytes.concat(padding);
  }

  /**
   * Coerce the input to {@link Bytes}.
   *
   * Inputs smaller than `this.size` are padded with zero bytes.
   */
  static from(data: (UInt8 | bigint | number)[] | Uint8Array | Bytes): Bytes {
    if (data instanceof Bytes) return data;
    if (this._size === undefined) {
      let Bytes_ = createBytes(data.length);
      return Bytes_.from(data);
    }
    return new this([...data].map(UInt8.from));
  }

  toBytes(): Uint8Array {
    return Uint8Array.from(this.bytes.map((x) => x.toNumber()));
  }

  toFields() {
    return this.bytes.map((x) => x.value);
  }

  /**
   * Base64 encode bytes.
   */
  base64Encode(): Bytes {
    const uint8Bytes = this.bytes;

    // Convert each byte to its 8-bit binary representation and reverse endianness
    let plainBits: Bool[] = uint8Bytes
      .map((b) => b.value.toBits(8).reverse())
      .flat();

    // Calculate the bit padding required to make the total bits length a multiple of 6
    const bitPadding =
      plainBits.length % 6 !== 0 ? 6 - (plainBits.length % 6) : 0;

    // Add the required bit padding with 0 bits
    plainBits.push(...Array(bitPadding).fill(new Bool(false)));

    let encodedBytes: UInt8[] = [];

    // Process the bits 6 at a time and encode to Base64
    for (let i = 0; i < plainBits.length; i += 6) {
      // Slice the next 6 bits and reverse endianness
      let byteBits = plainBits.slice(i, i + 6).reverse();

      // Convert the 6-bit chunk to a UInt8 value for indexing the Base64 table
      const indexTableByte = new UInt8(Field.fromBits(byteBits).value);

      // Use the index to get the corresponding Base64 character and add to the result
      encodedBytes.push(base64ELookup(indexTableByte));
    }

    // Add '=' padding to the encoded output if required
    const paddingLength =
      uint8Bytes.length % 3 !== 0 ? 3 - (uint8Bytes.length % 3) : 0;
    encodedBytes.push(...Array(paddingLength).fill(UInt8.from(61)));

    return Bytes.from(encodedBytes);
  }

  /**
   * Decode Base64-encoded bytes.
   *
   * @param byteLength The length of the output decoded bytes.
   */
  base64Decode(byteLength: number): Bytes {
    const encodedB64Bytes = this.bytes;

    const charLength = encodedB64Bytes.length;
    assert(
      charLength % 4 === 0,
      'Input base64 byte length should be a multiple of 4!'
    );

    let decodedB64Bytes: UInt8[] = [];

    let bitsIn: Bool[][][] = Array.from({ length: charLength / 4 }, () => []);
    let bitsOut: Bool[][][] = Array.from({ length: charLength / 4 }, () =>
      Array.from({ length: 4 }, () => [])
    );

    let idx = 0;
    for (let i = 0; i < charLength; i += 4) {
      for (let j = 0; j < 4; j++) {
        const translated = base64DLookup(encodedB64Bytes[i + j]);
        bitsIn[i / 4][j] = translated.toBits(6);
      }

      // Convert from four 6-bit words to three 8-bit words, unpacking the base64 encoding
      bitsOut[i / 4][0] = [
        bitsIn[i / 4][1][4],
        bitsIn[i / 4][1][5],
        ...bitsIn[i / 4][0],
      ];

      for (let j = 0; j < 4; j++) {
        bitsOut[i / 4][1][j] = bitsIn[i / 4][2][j + 2];
        bitsOut[i / 4][1][j + 4] = bitsIn[i / 4][1][j];
      }

      bitsOut[i / 4][2] = [
        ...bitsIn[i / 4][3],
        bitsIn[i / 4][2][0],
        bitsIn[i / 4][2][1],
      ];

      for (let j = 0; j < 3; j++) {
        if (idx + j < byteLength) {
          decodedB64Bytes[idx + j] = new UInt8(
            Field.fromBits(bitsOut[i / 4][j]).value
          );
        }
      }
      idx += 3;
    }

    return Bytes.from(decodedB64Bytes);
  }

  /**
   * Create {@link Bytes} from a string.
   *
   * Inputs smaller than `this.size` are padded with zero bytes.
   */
  static fromString(s: string) {
    let bytes = new TextEncoder().encode(s);
    return this.from(bytes);
  }

  /**
   * Create random {@link Bytes} using secure builtin randomness.
   */
  static random() {
    let bytes = randomBytes(this.size);
    return this.from(bytes);
  }

  /**
   * Create {@link Bytes} from a hex string.
   *
   * Inputs smaller than `this.size` are padded with zero bytes.
   */
  static fromHex(xs: string): Bytes {
    let bytes = chunkString(xs, 2).map((s) => parseInt(s, 16));
    return this.from(bytes);
  }

  /**
   * Convert {@link Bytes} to a hex string.
   */
  toHex(): string {
    return this.bytes
      .map((x) => x.toBigInt().toString(16).padStart(2, '0'))
      .join('');
  }

  // dynamic subclassing infra
  static _size?: number;
  static _provable?: ProvablePureExtended<
    Bytes,
    { bytes: { value: string }[] }
  >;

  /**
   * The size of the {@link Bytes}.
   */
  static get size() {
    assert(this._size !== undefined, 'Bytes not initialized');
    return this._size;
  }

  get length() {
    return this.bytes.length;
  }

  /**
   * `Provable<Bytes>`
   */
  static get provable() {
    assert(this._provable !== undefined, 'Bytes not initialized');
    return this._provable;
  }
}

function createBytes(size: number): typeof Bytes {
  return class Bytes_ extends Bytes {
    static _size = size;
    static _provable = provableFromClass(Bytes_, {
      bytes: Provable.Array(UInt8, size),
    });
  };
}

/**
 * Decodes a Base64 character to its original value.
 * Adapted from the algorithm described in: http://0x80.pl/notesen/2016-01-17-sse-base64-decoding.html#vector-lookup-base
 *
 * @param input - The Base64 encoded byte to be decoded.
 * @returns - The corresponding decoded value as a Field.
 */
function base64DLookup(input: UInt8): Field {
  // Initialize a Field to validate if the input byte is a valid Base64 character
  let isValidBase64Chars = new Field(0);

  // ['A' - 'Z'] range
  const le_Z = input.lessThan(91);
  const ge_A = input.greaterThan(64);
  const range_AZ = le_Z.and(ge_A);
  const sum_AZ = range_AZ.toField().mul(input.value.sub(65));
  isValidBase64Chars = isValidBase64Chars.add(range_AZ.toField());

  // ['a' - 'z'] range
  const le_z = input.lessThan(123);
  const ge_a = input.greaterThan(96);
  const range_az = le_z.and(ge_a);
  const sum_az = range_az.toField().mul(input.value.sub(71)).add(sum_AZ);
  isValidBase64Chars = isValidBase64Chars.add(range_az.toField());

  // ['0' - '9'] range
  const le_9 = input.lessThan(58);
  const ge_0 = input.greaterThan(47);
  const range_09 = le_9.and(ge_0);
  const sum_09 = range_09.toField().mul(input.value.add(4)).add(sum_az);
  isValidBase64Chars = isValidBase64Chars.add(range_09.toField());

  // '+' character
  const equal_plus = input.value.equals(43);
  const sum_plus = equal_plus.toField().mul(input.value.add(19)).add(sum_09);
  isValidBase64Chars = isValidBase64Chars.add(equal_plus.toField());

  // '/' character
  const equal_slash = input.value.equals(47);
  const sum_slash = equal_slash
    .toField()
    .mul(input.value.add(16))
    .add(sum_plus);
  isValidBase64Chars = isValidBase64Chars.add(equal_slash.toField());

  // '=' character
  const equal_eqsign = input.value.equals(61);
  isValidBase64Chars = isValidBase64Chars.add(equal_eqsign.toField());

  // Validate if input contains only valid Base64 characters
  isValidBase64Chars.assertEquals(
    1,
    'Please provide Base64-encoded bytes containing only alphanumeric characters and +/='
  );

  return sum_slash;
}

/**
 * Encodes a byte into its Base64 character representation.
 *
 * @param input - The byte to be encoded to Base64.
 * @returns - The corresponding Base64 encoded character as a UInt8.
 */
function base64ELookup(input: UInt8): UInt8 {
  // Initialize a Field to validate if the input byte is included in the Base64 index table
  let isValidBase64Chars = new Field(0);

  // ['A', 'Z'] - Note: Remove greater than zero check because a UInt8 byte is always positive
  const le_Z = input.lessThanOrEqual(25);
  const range_AZ = le_Z;
  const sum_AZ = range_AZ.toField().mul(input.value.add(65));
  isValidBase64Chars = isValidBase64Chars.add(range_AZ.toField());

  // ['a', 'z']
  const le_z = input.lessThanOrEqual(51);
  const ge_a = input.greaterThanOrEqual(26);
  const range_az = le_z.and(ge_a);
  const sum_az = range_az.toField().mul(input.value.add(71)).add(sum_AZ);
  isValidBase64Chars = isValidBase64Chars.add(range_az.toField());

  // ['0', '9']
  const le_9 = input.lessThanOrEqual(61);
  const ge_0 = input.greaterThanOrEqual(52);
  const range_09 = le_9.and(ge_0);
  const sum_09 = range_09.toField().mul(input.value.sub(4)).add(sum_az);
  isValidBase64Chars = isValidBase64Chars.add(range_09.toField());

  // '+'
  const equal_plus = input.value.equals(62);
  const sum_plus = equal_plus.toField().mul(input.value.sub(19)).add(sum_09);
  isValidBase64Chars = isValidBase64Chars.add(equal_plus.toField());

  // '/'
  const equal_slash = input.value.equals(63);
  const sum_slash = equal_slash
    .toField()
    .mul(input.value.sub(16))
    .add(sum_plus);
  isValidBase64Chars = isValidBase64Chars.add(equal_slash.toField());

  // Validate if input contains only valid base64 characters
  isValidBase64Chars.assertEquals(
    1,
    'Invalid character detected: The input contains a byte that is not present in the BASE64 index table!'
  );

  return new UInt8(sum_slash.value);
}
