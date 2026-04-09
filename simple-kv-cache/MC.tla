----------------------------------- MODULE MC -----------------------------------
EXTENDS Integers

KEYS == 0..(2^32 - 1)
VALUES == 0..(2^32 - 1)
TIMESTAMPS == 0..(24 * 60 * 60)
DELTA == 300

VARIABLES
    \* The global clock.
    \* @type: Int;
    now,
    \* The key-value store, mapping keys to values and their timestamps.
    \* @type: Int -> { val: Int, ts: Int };
    store,
    \* The cache, mapping keys to pairs of value and timestamp.
    \* @type: Int -> { val: Int, ts: Int };
    cache,
    \* Requests from the cache to the store.
    \* @type: Set({ key: Int, ts: Int });
    requests,
    \* Replies from the store to the cache.
    \* @type: { key: Int, ts: Int } -> { val: Int, ts: Int };
    replies,
    \* The history of all writes to the store, to write invariants.
    \* @type: Seq({ key: Int, val: Int, ts: Int });
    writes_history

INSTANCE SimpleKVCache
==========================================================================
