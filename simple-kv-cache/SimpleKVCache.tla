----------------------------------------- MODULE SimpleKVCache -----------------------------------------

(*
 * A simple model of a key-value store with a TTL-based cache on top of it. This
 * does not come from any particular system. The main point is to have an
 * easy-to-read example that also has meaningful behavior. This example
 * demonstrates the trade-off between bounded model checking and randomized
 * symbolic execution.
 * 
 * Igor Konnov, 2026
 * 
 * This specification is inspired by the following blog post about Facebook's
 * cache design:
 * 
 * https://engineering.fb.com/2022/06/08/core-infra/cache-made-consistent/
 *)
 EXTENDS Integers, Sequences
 
CONSTANTS
    \* The set of potential keys in the key-value store.
    \* @type: Set(Int);
    KEYS,
    \* The set of potential values in the key-value store.
    \* @type: Set(Int);
    VALUES,
    \* The set of of all timestamps.
    \* @type: Set(Int);
    TIMESTAMPS,
    \* Maximal message delivery time (if delivered at all).
    \* @type: Int;
    DELTA

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

\* How long a cache entry is valid after being fetched from the store.
TTL == 2 * DELTA

\* The initial state of the system: the store and cache are empty.
Init ==
    /\ now = 0
    /\ store = [k \in {} |-> [val |-> 0, ts |-> 0]]
    /\ cache = [k \in {} |-> [val |-> 0, ts |-> 0]]
    /\ requests = {}
    /\ replies = [  k \in {} |-> [val |-> 0, ts |-> 0]]
    /\ writes_history = <<>>

\* Another service updates the value in the store directly.
Put(key, val) ==
    Put::
    /\ store' = [ k \in DOMAIN store \union {key} |->
            IF k = key THEN [val |-> val, ts |-> now] ELSE store[k]
        ]
    /\ writes_history' = Append(writes_history, [key |-> key, val |-> val, ts |-> now])
    /\ UNCHANGED <<cache, requests, replies>>

\* The client retrieves the value for a key from the cache. No cache miss.
GetOk(key) ==
    GetOk::
    /\ key \in DOMAIN cache
    /\ LET entry == cache[key] IN
       /\ now < entry.ts + TTL
       /\ UNCHANGED <<store, cache, requests, replies, writes_history>>

\* The client misses the cache, so a request is sent to the store.
\* The cache entry is invalidated.
GetMiss(key) ==
    GetMiss::
    /\ key \in DOMAIN cache => (now > cache[key].ts + TTL)
    /\ requests' = requests \union { [key |-> key, ts |-> now] }
    /\ cache' = [ k \in DOMAIN cache \ {key} |-> cache[k]]
    /\ UNCHANGED <<store, replies, writes_history>>

\* The store replies to the cache with the value for a key.
SendReply(req) ==
    SendReply::
    /\ req \notin DOMAIN replies
    /\ req.key \in DOMAIN store
    /\ now <= req.ts + DELTA
    /\ LET entry == store[req.key] IN
       replies' = [ k \in DOMAIN replies \union {req} |->
            IF k = req THEN [val |-> entry.val, ts |-> now] ELSE replies[k]
          ]
    /\ UNCHANGED <<store, cache, requests, writes_history>>

\* The cache receives a reply from the store and updates its cache entry.
RecvReply(req) ==
    RecvReply::
    /\ req \in DOMAIN replies
    /\ LET reply == replies[req] IN
       /\ now <= reply.ts + DELTA
       /\ cache' = [ k \in DOMAIN cache \union {req.key} |->
            IF k = req.key THEN [val |-> reply.val, ts |-> now] ELSE cache[k]
          ]
    /\ UNCHANGED <<store, requests, replies, writes_history>>

\* All possible next states of the system.
Next ==
    /\ \E ts \in TIMESTAMPS:
        ts > now /\ now' = ts
    /\ \/ \E key \in KEYS, val \in VALUES: Put(key, val)
       \/ \E key \in KEYS: GetOk(key)
       \/ \E key \in KEYS: GetMiss(key)
       \/ \E req \in requests: SendReply(req)
       \/ \E req \in DOMAIN replies: RecvReply(req)

\* A naive invariant: the cache always has the same value as the store for all keys in the cache.
\* (This is not true in this system, but it is a good starting point for debugging.)
Inv1 ==
    \A key \in DOMAIN cache:
        /\ key \in DOMAIN store
        /\ LET cache_entry == cache[key]
               store_entry == store[key] IN
           (cache_entry.ts >= store_entry.ts) => cache_entry.val = store_entry.val

\* A better invariant: the cache has a value from the store's past.
\* (It does not tell us anything about the freshness of the cache entry.)
Inv2 ==
    \A key \in DOMAIN cache:
        /\ key \in DOMAIN store
        /\ LET cache_entry == cache[key] IN
           \E i \in DOMAIN writes_history:
               LET write == writes_history[i] IN
               /\ write.key = key
               /\ write.val = cache_entry.val
               /\ write.ts <= cache_entry.ts

\* Unsuccessfull improvement of Inv2: the cache has a value from the store's past, and there is no
\* later write to the same key with a different value.
Inv3 ==
    \A key \in DOMAIN cache:
        /\ key \in DOMAIN store
        /\ LET cache_entry == cache[key] IN
           \E i \in DOMAIN writes_history:
               LET write == writes_history[i] IN
               /\ write.key = key
               /\ write.val = cache_entry.val
               /\ write.ts <= cache_entry.ts
               \* if there is a later write to the same key with a different value, then
               \* it cannot be older than TTL time units 
               /\ \A j \in DOMAIN writes_history:
                    LET other_write == writes_history[j] IN
                    \/ other_write.key /= key
                    \/ other_write.val = write.val
                    \/ other_write.ts >= cache_entry.ts
                    \/ other_write.ts < write.ts

\* A more precise invariant: the cache has a value from the store's past, and there is no
\* later write to the same key that is older than TTL time units from the cache entry.
Inv4 ==
    \A key \in DOMAIN cache:
        /\ key \in DOMAIN store
        /\ LET cache_entry == cache[key] IN
           \E i \in DOMAIN writes_history:
               LET write == writes_history[i] IN
               /\ write.key = key
               /\ write.val = cache_entry.val
               /\ write.ts <= cache_entry.ts
               \* if there is a later write to the same key with a different value, then
               \* it cannot be older than TTL time units 
               /\ \A j \in DOMAIN writes_history:
                    LET other_write == writes_history[j] IN
                    \/ other_write.key /= key
                    \/ other_write.val = write.val
                    \/ other_write.ts \notin (write.ts + 1)..(cache_entry.ts - TTL)

========================================================================================================