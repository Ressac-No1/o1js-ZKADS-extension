import {
  GenericHashInput,
  GenericProvable,
  GenericProvablePure,
  GenericProvableExtended,
} from './generic.js';

export { createProvable, ProvableConstructor };

type ProvableConstructor<Field> = <A>(
  typeObj: A,
  options?: { customObjectKeys?: string[]; isPure?: boolean }
) => GenericProvableExtended<InferCircuitValue<A, Field>, InferJson<A>, Field>;

function createProvable<Field>(): ProvableConstructor<Field> {
  type ProvableExtended<T, TJson = JSONValue> = GenericProvableExtended<
    T,
    TJson,
    Field
  >;
  type HashInput = GenericHashInput<Field>;
  const HashInput = {
    get empty() {
      return {};
    },
    append(input1: HashInput, input2: HashInput): HashInput {
      if (input2.fields !== undefined) {
        (input1.fields ??= []).push(...input2.fields);
      }
      if (input2.packed !== undefined) {
        (input1.packed ??= []).push(...input2.packed);
      }
      return input1;
    },
  };

  let complexTypes = new Set(['object', 'function']);

  function provable<A>(
    typeObj: A,
    options?: { customObjectKeys?: string[]; isPure?: boolean }
  ): ProvableExtended<InferCircuitValue<A, Field>, InferJson<A>> {
    type T = InferCircuitValue<A, Field>;
    type J = InferJson<A>;
    let objectKeys =
      typeof typeObj === 'object' && typeObj !== null
        ? options?.customObjectKeys ?? Object.keys(typeObj).sort()
        : [];
    let nonCircuitPrimitives = new Set([
      Number,
      String,
      Boolean,
      BigInt,
      null,
      undefined,
    ]);
    if (
      !nonCircuitPrimitives.has(typeObj as any) &&
      !complexTypes.has(typeof typeObj)
    ) {
      throw Error(`provable: unsupported type "${typeObj}"`);
    }

    function sizeInFields(typeObj: any): number {
      if (nonCircuitPrimitives.has(typeObj)) return 0;
      if (Array.isArray(typeObj))
        return typeObj.map(sizeInFields).reduce((a, b) => a + b, 0);
      if ('sizeInFields' in typeObj) return typeObj.sizeInFields();
      return Object.values(typeObj)
        .map(sizeInFields)
        .reduce((a, b) => a + b, 0);
    }
    function toFields(typeObj: any, obj: any, isToplevel = false): Field[] {
      if (nonCircuitPrimitives.has(typeObj)) return [];
      if (!complexTypes.has(typeof typeObj) || typeObj === null) return [];
      if (Array.isArray(typeObj))
        return typeObj.map((t, i) => toFields(t, obj[i])).flat();
      if ('toFields' in typeObj) return typeObj.toFields(obj);
      return (isToplevel ? objectKeys : Object.keys(typeObj).sort())
        .map((k) => toFields(typeObj[k], obj[k]))
        .flat();
    }
    function toAuxiliary(typeObj: any, obj?: any, isToplevel = false): any[] {
      if (typeObj === Number) return [obj ?? 0];
      if (typeObj === String) return [obj ?? ''];
      if (typeObj === Boolean) return [obj ?? false];
      if (typeObj === BigInt) return [obj ?? 0n];
      if (typeObj === undefined || typeObj === null) return [];
      if (Array.isArray(typeObj))
        return typeObj.map((t, i) => toAuxiliary(t, obj?.[i]));
      if ('toAuxiliary' in typeObj) return typeObj.toAuxiliary(obj);
      return (isToplevel ? objectKeys : Object.keys(typeObj).sort()).map((k) =>
        toAuxiliary(typeObj[k], obj?.[k])
      );
    }
    function toInput(typeObj: any, obj: any, isToplevel = false): HashInput {
      if (nonCircuitPrimitives.has(typeObj)) return {};
      if (Array.isArray(typeObj)) {
        return typeObj
          .map((t, i) => toInput(t, obj[i]))
          .reduce(HashInput.append, {});
      }
      if ('toInput' in typeObj) return typeObj.toInput(obj) as HashInput;
      if ('toFields' in typeObj) {
        return { fields: typeObj.toFields(obj) };
      }
      return (isToplevel ? objectKeys : Object.keys(typeObj).sort())
        .map((k) => toInput(typeObj[k], obj[k]))
        .reduce(HashInput.append, {});
    }
    function toJSON(typeObj: any, obj: any, isToplevel = false): JSONValue {
      if (typeObj === BigInt) return obj.toString();
      if (typeObj === String || typeObj === Number || typeObj === Boolean)
        return obj;
      if (typeObj === undefined || typeObj === null) return null;
      if (!complexTypes.has(typeof typeObj) || typeObj === null)
        return obj ?? null;
      if (Array.isArray(typeObj))
        return typeObj.map((t, i) => toJSON(t, obj[i]));
      if ('toJSON' in typeObj) return typeObj.toJSON(obj);
      return Object.fromEntries(
        (isToplevel ? objectKeys : Object.keys(typeObj).sort()).map((k) => [
          k,
          toJSON(typeObj[k], obj[k]),
        ])
      );
    }
    function fromFields(
      typeObj: any,
      fields: Field[],
      aux: any[] = [],
      isToplevel = false
    ): any {
      if (
        typeObj === Number ||
        typeObj === String ||
        typeObj === Boolean ||
        typeObj === BigInt
      )
        return aux[0];
      if (typeObj === undefined || typeObj === null) return typeObj;
      if (!complexTypes.has(typeof typeObj)) return null;
      if (Array.isArray(typeObj)) {
        let array: any[] = [];
        let i = 0;
        let offset = 0;
        for (let subObj of typeObj) {
          let size = sizeInFields(subObj);
          array.push(
            fromFields(subObj, fields.slice(offset, offset + size), aux[i])
          );
          offset += size;
          i++;
        }
        return array;
      }
      if ('fromFields' in typeObj) return typeObj.fromFields(fields, aux);
      let keys = isToplevel ? objectKeys : Object.keys(typeObj).sort();
      let values = fromFields(
        keys.map((k) => typeObj[k]),
        fields,
        aux
      );
      return Object.fromEntries(keys.map((k, i) => [k, values[i]]));
    }
    function fromJSON(typeObj: any, json: any, isToplevel = false): any {
      if (typeObj === BigInt) return BigInt(json as string);
      if (typeObj === String || typeObj === Number || typeObj === Boolean)
        return json;
      if (typeObj === null) return undefined;
      if (!complexTypes.has(typeof typeObj)) return json ?? undefined;
      if (Array.isArray(typeObj))
        return typeObj.map((t, i) => fromJSON(t, json[i]));
      if ('fromJSON' in typeObj) return typeObj.fromJSON(json);
      let keys = isToplevel ? objectKeys : Object.keys(typeObj).sort();
      let values = fromJSON(
        keys.map((k) => typeObj[k]),
        json
      );
      return Object.fromEntries(keys.map((k, i) => [k, values[i]]));
    }
    function check(typeObj: any, obj: any, isToplevel = false): void {
      if (nonCircuitPrimitives.has(typeObj)) return;
      if (Array.isArray(typeObj))
        return typeObj.forEach((t, i) => check(t, obj[i]));
      if ('check' in typeObj) return typeObj.check(obj);
      return (isToplevel ? objectKeys : Object.keys(typeObj).sort()).forEach(
        (k) => check(typeObj[k], obj[k])
      );
    }
    if (options?.isPure === true) {
      return {
        sizeInFields: () => sizeInFields(typeObj),
        toFields: (obj: T) => toFields(typeObj, obj, true),
        toAuxiliary: () => [],
        fromFields: (fields: Field[]) =>
          fromFields(typeObj, fields, [], true) as T,
        toInput: (obj: T) => toInput(typeObj, obj, true),
        toJSON: (obj: T) => toJSON(typeObj, obj, true) as J,
        fromJSON: (json: J) => fromJSON(typeObj, json, true),
        check: (obj: T) => check(typeObj, obj, true),
      };
    }
    return {
      sizeInFields: () => sizeInFields(typeObj),
      toFields: (obj: T) => toFields(typeObj, obj, true),
      toAuxiliary: (obj?: T) => toAuxiliary(typeObj, obj, true),
      fromFields: (fields: Field[], aux: any[]) =>
        fromFields(typeObj, fields, aux, true) as T,
      toInput: (obj: T) => toInput(typeObj, obj, true),
      toJSON: (obj: T) => toJSON(typeObj, obj, true) as J,
      fromJSON: (json: J) => fromJSON(typeObj, json, true),
      check: (obj: T) => check(typeObj, obj, true),
    };
  }

  return provable;
}

// some type inference helpers

type JSONValue =
  | number
  | string
  | boolean
  | null
  | Array<JSONValue>
  | { [key: string]: JSONValue };

type Constructor<T> = new (...args: any) => T;

type Tuple<T> = [T, ...T[]] | [];

type Primitive =
  | typeof String
  | typeof Number
  | typeof Boolean
  | typeof BigInt
  | null
  | undefined;
type InferPrimitive<P extends Primitive> = P extends typeof String
  ? string
  : P extends typeof Number
  ? number
  : P extends typeof Boolean
  ? boolean
  : P extends typeof BigInt
  ? bigint
  : P extends null
  ? null
  : P extends undefined
  ? undefined
  : any;
type InferPrimitiveJson<P extends Primitive> = P extends typeof String
  ? string
  : P extends typeof Number
  ? number
  : P extends typeof Boolean
  ? boolean
  : P extends typeof BigInt
  ? string
  : P extends null
  ? null
  : P extends undefined
  ? null
  : JSONValue;

type InferCircuitValue<A, Field> = A extends Constructor<infer U>
  ? A extends GenericProvable<U, Field>
    ? U
    : InferCircuitValueBase<A, Field>
  : InferCircuitValueBase<A, Field>;

type InferCircuitValueBase<A, Field> = A extends GenericProvable<infer U, Field>
  ? U
  : A extends Primitive
  ? InferPrimitive<A>
  : A extends Tuple<any>
  ? {
      [I in keyof A]: InferCircuitValue<A[I], Field>;
    }
  : A extends (infer U)[]
  ? InferCircuitValue<U, Field>[]
  : A extends Record<any, any>
  ? {
      [K in keyof A]: InferCircuitValue<A[K], Field>;
    }
  : never;

type WithJson<J> = { toJSON: (x: any) => J };

type InferJson<A> = A extends WithJson<infer J>
  ? J
  : A extends Primitive
  ? InferPrimitiveJson<A>
  : A extends Tuple<any>
  ? {
      [I in keyof A]: InferJson<A[I]>;
    }
  : A extends WithJson<infer U>[]
  ? U[]
  : A extends Record<any, any>
  ? {
      [K in keyof A]: InferJson<A[K]>;
    }
  : JSONValue;

type IsPure<A, Field> = IsPureBase<A, Field> extends true ? true : false;

type IsPureBase<A, Field> = A extends GenericProvablePure<any, Field>
  ? true
  : A extends GenericProvable<any, Field>
  ? false
  : A extends Primitive
  ? false
  : A extends (infer U)[]
  ? IsPure<U, Field>
  : A extends Record<any, any>
  ? {
      [K in keyof A]: IsPure<A[K], Field>;
    }[keyof A]
  : false;
