import type { AccountUpdateLayout } from '../account_update.js';
import type { PublicKey } from '../signature.js';
import { Context } from '../global-context.js';

export { currentTransaction, CurrentTransaction, FetchMode };

type FetchMode = 'fetch' | 'cached' | 'test';
type CurrentTransaction = {
  sender?: PublicKey;
  layout: AccountUpdateLayout;
  fetchMode: FetchMode;
  isFinalRunOutsideCircuit: boolean;
  numberOfRuns: 0 | 1 | undefined;
};

let currentTransaction = Context.create<CurrentTransaction>();