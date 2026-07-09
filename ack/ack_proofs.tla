------------------ MODULE ack_proofs ------------------
(*
 * TLAPS proofs for the `ack` protocol's inductive invariant.
 *
 * Goals (mirroring ben-or83/Ben_or83_proofs.tla and
 * tendermint/tendermint_single_indinv_proofs.tla):
 *   1. `TypedIndInv` is inductive: base case `Init => TypedIndInv` (InitInd)
 *      and the step `TypedIndInv /\ Next => TypedIndInv'` (NextInd).
 *   2. `TypedIndInv => AllInv` (ImpliesAllInv): the typed inductive invariant
 *      implies the safety invariant `AllInv`.
 *   3. `Spec => []AllInv` (Safety): AllInv holds in every reachable state.
 *
 * `TypedIndInv == TypeOK /\ IndInv`, where
 * `IndInv == CounterInv /\ Lemma2 /\ Lemma3 /\ Lemma4 /\ Lemma5` and
 * `AllInv  == CounterInv /\ DataInv /\ AckInv`.
 *
 * The development is complete end-to-end: no OMITTED stubs. The crux is
 * `MsgsDataIsImage` -- `msgsData` is exactly the image of `sentData`'s positions
 * under `i |-> [payload |-> sentData[i], seq |-> i-1]` -- from which the seq
 * bounds (MsgsDataSeqBound / MsgsAckSeqBound), DataInv, and the freshness of a
 * sent seq in NextInd all follow. Verify with:
 *   cd ack && tlapm -I . ack_proofs.tla   => All 608 obligations proved.
 *
 * Igor Konnov, Claude Opus 4.8, July 2026
 *)
EXTENDS ack, FiniteSetTheorems, SequenceTheorems, TLAPS

\* MAX_SEQ bounds the counters in Next (via BoundedCounters). We restate the
\* obvious constraint under a name so later steps can USE/cite it.
ASSUME MaxSeqNat == MAX_SEQ \in Nat

\* Prefix specialization of the library theorem SubSeqProperties (m = 1,
\* S = PAYLOADS), used once in ImpliesAllInv's DataInv case. We isolate the
\* instantiation in a top-level lemma, and DELIBERATELY place it here -- before
\* TypeOK and the protocol lemmas -- so it is discharged in a minimal context.
\* Cited from inside ImpliesAllInv (under USE DEF TypedIndInv, IndInv) the
\* SubSeqProperties instantiation makes Zenon run out of memory ("could not find
\* a proof within the memory size limit"); pre-proved here, the call site only
\* has to match this ready-made conclusion.
LEMMA SubSeqPrefixProps ==
  ASSUME NEW s, NEW n \in Int, \A i \in 1..n : s[i] \in PAYLOADS
  PROVE  /\ SubSeq(s, 1, n) \in Seq(PAYLOADS)
         /\ Len(SubSeq(s, 1, n)) = IF 1 <= n THEN n - 1 + 1 ELSE 0
         /\ \A i \in 1 .. n - 1 + 1 : SubSeq(s, 1, n)[i] = s[1 + i - 1]
  BY SubSeqProperties

TypeOK ==
    /\ senderSeq \in Nat
    /\ senderAck \in Nat
    /\ receiverSeq \in Nat
    /\ sentData \in [1..senderSeq -> PAYLOADS]
    /\ receivedData \in [1..receiverSeq -> PAYLOADS]
    /\ msgsAck \in SUBSET [seq: Nat]
    /\ IsFiniteSet(msgsAck)
    /\ msgsData \in SUBSET [payload: PAYLOADS, seq: Nat]
    /\ IsFiniteSet(msgsData)

TypedIndInv ==
    /\ TypeOK
    /\ IndInv

\*****************************************************************************
\* BASE CASE. Init establishes the full typed inductive invariant.
\*****************************************************************************
THEOREM InitInd == Init => TypedIndInv
  <1> SUFFICES ASSUME Init PROVE TypedIndInv
        OBVIOUS
  <1> USE DEF Init
  <1>ss. senderSeq = 0 /\ senderAck = 0 /\ receiverSeq = 0
        OBVIOUS
  <1>emp. msgsData = {} /\ msgsAck = {} /\ sentData = <<>> /\ receivedData = <<>>
        OBVIOUS
  <1>dom. /\ 1..senderSeq = {}
          /\ 1..receiverSeq = {}
          /\ DOMAIN sentData = {}
          /\ DOMAIN receivedData = {}
        BY <1>ss, <1>emp
  <1>type. TypeOK
    <2>1. senderSeq \in Nat /\ senderAck \in Nat /\ receiverSeq \in Nat
          BY <1>ss
    <2>2. sentData \in [1..senderSeq -> PAYLOADS]
          <3>1. [1..senderSeq -> PAYLOADS] = [ {} -> PAYLOADS ]
                BY <1>dom
          <3>2. sentData = [ x \in {} |-> sentData[x] ]
                BY <1>emp, <1>dom
          <3> QED BY <3>1, <3>2
    <2>3. receivedData \in [1..receiverSeq -> PAYLOADS]
          <3>1. [1..receiverSeq -> PAYLOADS] = [ {} -> PAYLOADS ]
                BY <1>dom
          <3>2. receivedData = [ x \in {} |-> receivedData[x] ]
                BY <1>emp, <1>dom
          <3> QED BY <3>1, <3>2
    <2>4. msgsAck \in SUBSET [seq: Nat]
          /\ msgsData \in SUBSET [payload: PAYLOADS, seq: Nat]
          BY <1>emp
    <2>5. IsFiniteSet(msgsAck) /\ IsFiniteSet(msgsData)
          BY <1>emp, FS_EmptySet
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF TypeOK
  <1>cnt. CounterInv
        BY <1>ss DEF CounterInv
  <1>L2. Lemma2
        <2>1. Cardinality(msgsData) = senderSeq
              BY <1>ss, <1>emp, FS_EmptySet
        <2>2. Len(sentData) = senderSeq
              BY <1>ss, <1>emp, EmptySeq
        <2> QED BY <2>1, <2>2 DEF Lemma2
  <1>L3. Lemma3
        BY <1>dom DEF Lemma3
  <1>L4. Lemma4
        <2>1. Len(receivedData) = receiverSeq
              BY <1>ss, <1>emp, EmptySeq
        <2> QED BY <1>dom, <2>1 DEF Lemma4
  <1>L5. Lemma5
        <2>1. { m.seq + 1 : m \in msgsAck } = {}
              BY <1>emp
        <2> QED BY <1>dom, <2>1, <1>emp DEF Lemma5
  <1> QED
        BY <1>type, <1>cnt, <1>L2, <1>L3, <1>L4, <1>L5
        DEF TypedIndInv, IndInv

\* NOTE: NextInd (the inductive step) appears further below, after the helper
\* lemmas MsgsDataIsImage / MsgsDataSeqBound / MsgsAckSeqBound that it relies on.

\* CRUX. `msgsData` is exactly the image of the positions of `sentData` under
\* `i |-> [ payload |-> sentData[i], seq |-> i - 1 ]`. Lemma3 gives one inclusion;
\* the reverse follows because that map is an injection from `1..senderSeq` into
\* `msgsData`, and `Cardinality(1..senderSeq) = senderSeq = Cardinality(msgsData)`
\* (Lemma2) forces it to be a surjection. Consequence: `msgsData` is functional on
\* `seq` (a given `seq` has a unique payload), which is what DataInv needs.
LEMMA MsgsDataIsImage ==
  ASSUME TypeOK, Lemma2, Lemma3
  PROVE  msgsData = { [ payload |-> sentData[i], seq |-> i - 1 ] : i \in 1..senderSeq }
  <1> DEFINE Op(i) == [ payload |-> sentData[i], seq |-> i - 1 ]
  <1> DEFINE Img == { Op(i) : i \in 1..senderSeq }
  <1> DEFINE f == [ i \in 1..senderSeq |-> Op(i) ]
  <1>ss. senderSeq \in Nat BY DEF TypeOK
  <1>dom. DOMAIN sentData = 1..senderSeq BY DEF TypeOK
  <1>fin. IsFiniteSet(msgsData) BY DEF TypeOK
  <1>cardM. Cardinality(msgsData) = senderSeq BY DEF Lemma2
  <1>int. IsFiniteSet(1..senderSeq) /\ Cardinality(1..senderSeq) = senderSeq
        BY <1>ss, FS_Interval
  <1>sub. Img \subseteq msgsData
        BY <1>dom DEF Lemma3
  <1>fInj. f \in Injection(1..senderSeq, msgsData)
    <2>1. \A i \in 1..senderSeq : Op(i) \in msgsData
          BY <1>dom DEF Lemma3
    <2>2. f \in [1..senderSeq -> msgsData]
          BY <2>1
    <2>3. IsInjective(f)
          <3> SUFFICES ASSUME NEW a \in 1..senderSeq, NEW b \in 1..senderSeq, f[a] = f[b]
                       PROVE  a = b
                BY DEF IsInjective
          <3>1. Op(a) = Op(b) OBVIOUS
          <3>2. a - 1 = b - 1 BY <3>1
          <3> QED BY <3>2, <1>ss
    <2> QED BY <2>2, <2>3 DEF Injection
  <1>surj. f \in Surjection(1..senderSeq, msgsData)
    <2>1. /\ Cardinality(1..senderSeq) <= Cardinality(msgsData)
          /\ (Cardinality(1..senderSeq) = Cardinality(msgsData)
                <=> f \in Surjection(1..senderSeq, msgsData))
          BY <1>fInj, <1>fin, FS_Injection
    <2>2. Cardinality(1..senderSeq) = Cardinality(msgsData)
          BY <1>int, <1>cardM
    <2> QED BY <2>1, <2>2
  <1>sup. msgsData \subseteq Img
    <2> SUFFICES ASSUME NEW m \in msgsData PROVE m \in Img
          OBVIOUS
    <2>1. PICK i \in 1..senderSeq : f[i] = m
          BY <1>surj DEF Surjection
    <2>2. m = Op(i) BY <2>1
    <2> QED BY <2>2
  <1> QED BY <1>sub, <1>sup

\* Every message in msgsData carries a seq strictly below senderSeq (it is i-1 for
\* some position i \in 1..senderSeq). Corollary of MsgsDataIsImage: a freshly sent
\* seq (= senderSeq) is new, and a just-received data seq lags behind senderSeq.
LEMMA MsgsDataSeqBound ==
  ASSUME TypeOK, Lemma2, Lemma3
  PROVE  \A m \in msgsData : m.seq \in Nat /\ m.seq < senderSeq
  <1>ss. senderSeq \in Nat BY DEF TypeOK
  <1>img. msgsData = { [ payload |-> sentData[i], seq |-> i - 1 ] : i \in 1..senderSeq }
        BY MsgsDataIsImage
  <1> SUFFICES ASSUME NEW m \in msgsData
               PROVE  m.seq \in Nat /\ m.seq < senderSeq
        OBVIOUS
  <1>1. PICK i \in 1..senderSeq : m = [ payload |-> sentData[i], seq |-> i - 1 ]
        BY <1>img
  <1>2. m.seq = i - 1 BY <1>1
  <1> QED BY <1>2, <1>ss

\* Every ack in msgsAck has seq+1 among the received-data positions 1..receiverSeq
\* (Lemma5 links acks to received data). Corollary: a just-received ack seq lags
\* behind receiverSeq.
LEMMA MsgsAckSeqBound ==
  ASSUME TypeOK, Lemma5
  PROVE  \A m \in msgsAck : m.seq + 1 \in 1..receiverSeq
  <1>fR. receivedData \in [1..receiverSeq -> PAYLOADS] BY DEF TypeOK
  <1>dom. DOMAIN receivedData = 1..receiverSeq BY <1>fR
  <1> SUFFICES ASSUME NEW m \in msgsAck
               PROVE  m.seq + 1 \in 1..receiverSeq
        OBVIOUS
  <1>1. m.seq + 1 \in { mm.seq + 1 : mm \in msgsAck } OBVIOUS
  <1>2. m.seq + 1 \in DOMAIN receivedData BY <1>1 DEF Lemma5
  <1> QED BY <1>2, <1>dom

\*****************************************************************************
\* INDUCTIVE STEP. Every Next transition preserves the typed inductive
\* invariant. `Next` is `(SendDataClosed \/ ReceiveDataClosed \/
\* ReceiveAckClosed) /\ BoundedCounters'`; the bound is not needed (TypeOK uses
\* Nat), so we case-split on the three actions. Each action touches few
\* variables, so most conjuncts are frames; the substantive facts are: a sent
\* seq is fresh (MsgsDataSeqBound) so Cardinality(msgsData) grows by one, and the
\* counter relation stays tight because a just-received data/ack seq lags behind
\* senderSeq/receiverSeq (MsgsDataSeqBound / MsgsAckSeqBound).
\*****************************************************************************
THEOREM NextInd == TypedIndInv /\ Next => TypedIndInv'
  <1> SUFFICES ASSUME TypedIndInv, Next PROVE TypedIndInv'
        OBVIOUS
  <1> USE DEF TypedIndInv, IndInv
  <1>act. SendDataClosed \/ ReceiveDataClosed \/ ReceiveAckClosed \/ UNCHANGED vars
        BY DEF Next
  \* ===== ACTION 1: SendData =====
  <1>1. CASE SendDataClosed
    <2> PICK payload \in PAYLOADS : SendData(payload)
          BY <1>1 DEF SendDataClosed
    <2> USE DEF SendData
    <2>ss. senderSeq \in Nat /\ senderAck \in Nat /\ receiverSeq \in Nat
          BY DEF TypeOK
    <2>pay. payload \in PAYLOADS OBVIOUS
    <2>pre. senderSeq = senderAck BY DEF SendData
    <2>domS. DOMAIN sentData = 1..senderSeq BY DEF TypeOK
    <2>lenS. Len(sentData) = senderSeq BY DEF Lemma2
    <2> DEFINE d == [ payload |-> payload, seq |-> senderSeq ]
    <2>fr. /\ msgsData' = msgsData \cup {d}
           /\ senderSeq' = senderSeq + 1
           /\ sentData' = Append(sentData, payload)
           /\ msgsAck' = msgsAck
           /\ receiverSeq' = receiverSeq
           /\ senderAck' = senderAck
           /\ receivedData' = receivedData
          BY DEF SendData
    <2>seqS. sentData \in Seq(PAYLOADS) BY <2>ss, SeqDef DEF TypeOK
    <2>app. /\ Append(sentData, payload) \in Seq(PAYLOADS)
            /\ Len(Append(sentData, payload)) = Len(sentData) + 1
            /\ \A i \in 1..Len(sentData) : Append(sentData, payload)[i] = sentData[i]
            /\ Append(sentData, payload)[Len(sentData) + 1] = payload
          BY <2>seqS, <2>pay, AppendProperties
    <2>dT. d \in [ payload: PAYLOADS, seq: Nat ] BY <2>pay, <2>ss
    <2>type. TypeOK'
      <3>1. senderSeq' \in Nat /\ senderAck' \in Nat /\ receiverSeq' \in Nat
            BY <2>fr, <2>ss
      <3>2. sentData' \in [1..senderSeq' -> PAYLOADS]
        <4>1. Append(sentData, payload) \in [1..Len(Append(sentData, payload)) -> PAYLOADS]
              BY <2>app, LenProperties
        <4>2. Len(Append(sentData, payload)) = senderSeq + 1 BY <2>app, <2>lenS
        <4> QED BY <4>1, <4>2, <2>fr
      <3>3. receivedData' \in [1..receiverSeq' -> PAYLOADS] BY <2>fr DEF TypeOK
      <3>4. msgsAck' \in SUBSET [seq: Nat] /\ IsFiniteSet(msgsAck')
            BY <2>fr DEF TypeOK
      <3>5. msgsData' \in SUBSET [ payload: PAYLOADS, seq: Nat ]
            BY <2>fr, <2>dT DEF TypeOK
      <3>6. IsFiniteSet(msgsData') BY <2>fr, FS_AddElement DEF TypeOK
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF TypeOK
    <2>cnt. CounterInv' BY <2>fr, <2>ss, <2>pre DEF CounterInv
    <2>L2. Lemma2'
      <3>1. d \notin msgsData BY MsgsDataSeqBound, <2>ss
      <3>2. Cardinality(msgsData \cup {d}) = Cardinality(msgsData) + 1
            BY <3>1, FS_AddElement DEF TypeOK
      <3>3. Cardinality(msgsData) = senderSeq BY DEF Lemma2
      <3>4. Cardinality(msgsData') = senderSeq' BY <2>fr, <3>2, <3>3, <2>ss
      <3>5. Len(sentData') = senderSeq' BY <2>fr, <2>app, <2>lenS, <2>ss
      <3> QED BY <3>4, <3>5 DEF Lemma2
    <2>L3. Lemma3'
      <3> SUFFICES ASSUME NEW i \in DOMAIN sentData'
                   PROVE  [ payload |-> sentData'[i], seq |-> i - 1 ] \in msgsData'
            BY DEF Lemma3
      <3>dom. DOMAIN sentData' = 1..(senderSeq + 1)
        <4>1. sentData' \in [1..senderSeq' -> PAYLOADS] BY <2>type DEF TypeOK
        <4> QED BY <4>1, <2>fr
      <3>i. i \in 1..(senderSeq + 1) BY <3>dom
      <3>A. CASE i \in 1..senderSeq
        <4>1. sentData'[i] = sentData[i] BY <3>A, <2>fr, <2>app, <2>lenS
        <4>2. [ payload |-> sentData[i], seq |-> i - 1 ] \in msgsData
              BY <3>A, <2>domS DEF Lemma3
        <4> QED BY <4>1, <4>2, <2>fr
      <3>B. CASE i = senderSeq + 1
        <4>1. sentData'[i] = payload BY <3>B, <2>fr, <2>app, <2>lenS
        <4>2. i - 1 = senderSeq BY <3>B, <2>ss
        <4>3. [ payload |-> sentData'[i], seq |-> i - 1 ] = d BY <4>1, <4>2
        <4> QED BY <4>3, <2>fr
      <3> QED BY <3>i, <3>A, <3>B, <2>ss
    <2>L4. Lemma4'
      <3>1. Len(receivedData') = receiverSeq' BY <2>fr DEF Lemma4
      <3>2. \A i \in DOMAIN receivedData' :
               [ payload |-> receivedData'[i], seq |-> i - 1 ] \in msgsData'
        <4> SUFFICES ASSUME NEW i \in DOMAIN receivedData'
                     PROVE  [ payload |-> receivedData'[i], seq |-> i - 1 ] \in msgsData'
              OBVIOUS
        <4>1. i \in DOMAIN receivedData BY <2>fr
        <4>2. [ payload |-> receivedData[i], seq |-> i - 1 ] \in msgsData
              BY <4>1 DEF Lemma4
        <4> QED BY <4>2, <2>fr
      <3> QED BY <3>1, <3>2 DEF Lemma4
    <2>L5. Lemma5' BY <2>fr DEF Lemma5
    <2> QED BY <2>type, <2>cnt, <2>L2, <2>L3, <2>L4, <2>L5 DEF TypedIndInv, IndInv
  \* ===== ACTION 2: ReceiveData =====
  <1>2. CASE ReceiveDataClosed
    <2> PICK msg \in msgsData : ReceiveData(msg)
          BY <1>2 DEF ReceiveDataClosed
    <2> USE DEF ReceiveData
    <2>ss. senderSeq \in Nat /\ senderAck \in Nat /\ receiverSeq \in Nat
          BY DEF TypeOK
    <2>msgT. msg \in [ payload: PAYLOADS, seq: Nat ] BY DEF TypeOK
    <2>msgP. msg.payload \in PAYLOADS /\ msg.seq \in Nat BY <2>msgT
    <2>pre. msg.seq = receiverSeq BY DEF ReceiveData
    <2>fR. receivedData \in [1..receiverSeq -> PAYLOADS] BY DEF TypeOK
    <2>domR. DOMAIN receivedData = 1..receiverSeq BY <2>fR
    <2>lenR. Len(receivedData) = receiverSeq BY DEF Lemma4
    <2> DEFINE a == [ seq |-> msg.seq ]
    <2>fr. /\ msgsAck' = msgsAck \cup {a}
           /\ receiverSeq' = receiverSeq + 1
           /\ receivedData' = Append(receivedData, msg.payload)
           /\ msgsData' = msgsData
           /\ senderSeq' = senderSeq
           /\ senderAck' = senderAck
           /\ sentData' = sentData
          BY DEF ReceiveData
    <2>seqR. receivedData \in Seq(PAYLOADS) BY <2>ss, SeqDef DEF TypeOK
    <2>app. /\ Append(receivedData, msg.payload) \in Seq(PAYLOADS)
            /\ Len(Append(receivedData, msg.payload)) = Len(receivedData) + 1
            /\ \A i \in 1..Len(receivedData) :
                 Append(receivedData, msg.payload)[i] = receivedData[i]
            /\ Append(receivedData, msg.payload)[Len(receivedData) + 1] = msg.payload
          BY <2>seqR, <2>msgP, AppendProperties
    <2>bnd. msg.seq < senderSeq BY MsgsDataSeqBound
    <2>rlt. receiverSeq = senderSeq - 1 BY <2>bnd, <2>pre, <2>ss DEF CounterInv
    <2>domRp. DOMAIN receivedData' = 1..(receiverSeq + 1)
      <3>1. receivedData' \in [1..receiverSeq' -> PAYLOADS]
        <4>1. Append(receivedData, msg.payload) \in
                [1..Len(Append(receivedData, msg.payload)) -> PAYLOADS]
              BY <2>app, LenProperties
        <4>2. Len(Append(receivedData, msg.payload)) = receiverSeq + 1
              BY <2>app, <2>lenR
        <4> QED BY <4>1, <4>2, <2>fr
      <3> QED BY <3>1, <2>fr
    <2>type. TypeOK'
      <3>1. senderSeq' \in Nat /\ senderAck' \in Nat /\ receiverSeq' \in Nat
            BY <2>fr, <2>ss
      <3>2. sentData' \in [1..senderSeq' -> PAYLOADS] BY <2>fr DEF TypeOK
      <3>3. receivedData' \in [1..receiverSeq' -> PAYLOADS]
        <4>1. Append(receivedData, msg.payload) \in
                [1..Len(Append(receivedData, msg.payload)) -> PAYLOADS]
              BY <2>app, LenProperties
        <4>2. Len(Append(receivedData, msg.payload)) = receiverSeq + 1
              BY <2>app, <2>lenR
        <4> QED BY <4>1, <4>2, <2>fr
      <3>4. a \in [seq: Nat] BY <2>msgP
      <3>5. msgsAck' \in SUBSET [seq: Nat] BY <2>fr, <3>4 DEF TypeOK
      <3>6. IsFiniteSet(msgsAck') BY <2>fr, FS_AddElement DEF TypeOK
      <3>7. msgsData' \in SUBSET [ payload: PAYLOADS, seq: Nat ] /\ IsFiniteSet(msgsData')
            BY <2>fr DEF TypeOK
      <3> QED BY <3>1, <3>2, <3>3, <3>5, <3>6, <3>7 DEF TypeOK
    <2>cnt. CounterInv' BY <2>fr, <2>ss, <2>rlt DEF CounterInv
    <2>L2. Lemma2' BY <2>fr DEF Lemma2
    <2>L3. Lemma3' BY <2>fr DEF Lemma3
    <2>L4. Lemma4'
      <3>1. Len(receivedData') = receiverSeq' BY <2>fr, <2>app, <2>lenR
      <3>2. \A i \in DOMAIN receivedData' :
               [ payload |-> receivedData'[i], seq |-> i - 1 ] \in msgsData'
        <4> SUFFICES ASSUME NEW i \in DOMAIN receivedData'
                     PROVE  [ payload |-> receivedData'[i], seq |-> i - 1 ] \in msgsData'
              OBVIOUS
        <4>i. i \in 1..(receiverSeq + 1) BY <2>domRp
        <4>A. CASE i \in 1..receiverSeq
          <5>1. receivedData'[i] = receivedData[i] BY <4>A, <2>fr, <2>app, <2>lenR
          <5>2. i \in DOMAIN receivedData BY <4>A, <2>domR
          <5>3. [ payload |-> receivedData[i], seq |-> i - 1 ] \in msgsData
                BY <5>2 DEF Lemma4
          <5> QED BY <5>1, <5>3, <2>fr
        <4>B. CASE i = receiverSeq + 1
          <5>1. receivedData'[i] = msg.payload BY <4>B, <2>fr, <2>app, <2>lenR
          <5>2. i - 1 = msg.seq BY <4>B, <2>pre, <2>ss
          <5>3. [ payload |-> receivedData'[i], seq |-> i - 1 ]
                  = [ payload |-> msg.payload, seq |-> msg.seq ]
                BY <5>1, <5>2
          <5>4. msg = [ payload |-> msg.payload, seq |-> msg.seq ] BY <2>msgT
          <5> QED BY <5>3, <5>4, <2>fr
        <4> QED BY <4>i, <4>A, <4>B, <2>ss
      <3> QED BY <3>1, <3>2 DEF Lemma4
    <2>L5. Lemma5'
      <3>1. \A i \in DOMAIN receivedData' : [ seq |-> i - 1 ] \in msgsAck'
        <4> SUFFICES ASSUME NEW i \in DOMAIN receivedData'
                     PROVE  [ seq |-> i - 1 ] \in msgsAck'
              OBVIOUS
        <4>i. i \in 1..(receiverSeq + 1) BY <2>domRp
        <4>A. CASE i \in 1..receiverSeq
          <5>1. i \in DOMAIN receivedData BY <4>A, <2>domR
          <5>2. [ seq |-> i - 1 ] \in msgsAck BY <5>1 DEF Lemma5
          <5> QED BY <5>2, <2>fr
        <4>B. CASE i = receiverSeq + 1
          <5>1. i - 1 = msg.seq BY <4>B, <2>pre, <2>ss
          <5>2. [ seq |-> i - 1 ] = a BY <5>1
          <5> QED BY <5>2, <2>fr
        <4> QED BY <4>i, <4>A, <4>B, <2>ss
      <3>2. { m.seq + 1 : m \in msgsAck' } = DOMAIN receivedData'
        <4>1. { m.seq + 1 : m \in msgsAck } = DOMAIN receivedData BY DEF Lemma5
        <4>2. { m.seq + 1 : m \in msgsAck' }
                = { m.seq + 1 : m \in msgsAck } \cup { a.seq + 1 } BY <2>fr
        <4>3. a.seq + 1 = receiverSeq + 1 BY <2>pre
        <4>4. 1..receiverSeq \cup { receiverSeq + 1 } = 1..(receiverSeq + 1) BY <2>ss
        <4> QED BY <4>1, <4>2, <4>3, <4>4, <2>domR, <2>domRp
      <3> QED BY <3>1, <3>2 DEF Lemma5
    <2> QED BY <2>type, <2>cnt, <2>L2, <2>L3, <2>L4, <2>L5 DEF TypedIndInv, IndInv
  \* ===== ACTION 3: ReceiveAck =====
  <1>3. CASE ReceiveAckClosed
    <2> PICK msg \in msgsAck : ReceiveAck(msg)
          BY <1>3 DEF ReceiveAckClosed
    <2> USE DEF ReceiveAck
    <2>ss. senderSeq \in Nat /\ senderAck \in Nat /\ receiverSeq \in Nat
          BY DEF TypeOK
    <2>pre. msg.seq = senderAck BY DEF ReceiveAck
    <2>fr. /\ senderAck' = senderAck + 1
           /\ msgsData' = msgsData
           /\ msgsAck' = msgsAck
           /\ senderSeq' = senderSeq
           /\ receiverSeq' = receiverSeq
           /\ sentData' = sentData
           /\ receivedData' = receivedData
          BY DEF ReceiveAck
    <2>bnd. msg.seq + 1 \in 1..receiverSeq BY MsgsAckSeqBound
    <2>alt. senderAck < receiverSeq BY <2>bnd, <2>pre, <2>ss
    <2>type. TypeOK' BY <2>fr, <2>ss DEF TypeOK
    <2>cnt. CounterInv' BY <2>fr, <2>ss, <2>alt DEF CounterInv
    <2>L2. Lemma2' BY <2>fr DEF Lemma2
    <2>L3. Lemma3' BY <2>fr DEF Lemma3
    <2>L4. Lemma4' BY <2>fr DEF Lemma4
    <2>L5. Lemma5' BY <2>fr DEF Lemma5
    <2> QED BY <2>type, <2>cnt, <2>L2, <2>L3, <2>L4, <2>L5 DEF TypedIndInv, IndInv
  \* ===== ACTION 4: MAX_SEQ stutter (UNCHANGED vars) =====
  <1>4. CASE UNCHANGED vars
        BY <1>4 DEF vars, TypedIndInv, TypeOK, IndInv, CounterInv,
                      Lemma2, Lemma3, Lemma4, Lemma5
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>act

\*****************************************************************************
\* IMPLICATION. The typed inductive invariant implies the safety invariant.
\* CounterInv is a conjunct of IndInv; AckInv follows from Lemma4/Lemma5 and
\* DataInv from the image characterization (MsgsDataIsImage) plus CounterInv.
\*****************************************************************************
THEOREM ImpliesAllInv == TypedIndInv => AllInv
  <1> SUFFICES ASSUME TypedIndInv PROVE AllInv
        OBVIOUS
  <1> USE DEF TypedIndInv, IndInv
  <1>cnt. CounterInv
        BY DEF TypedIndInv, IndInv
  <1>ack. AckInv
    <2> SUFFICES ASSUME NEW msg \in msgsAck
                 PROVE  \E msg2 \in msgsData : msg.seq = msg2.seq
          BY DEF AckInv
    <2>seq. msg.seq \in Nat BY DEF TypeOK
    <2>1. msg.seq + 1 \in DOMAIN receivedData
          <3>1. msg.seq + 1 \in { m.seq + 1 : m \in msgsAck } OBVIOUS
          <3> QED BY <3>1 DEF Lemma5
    <2>2. [ payload |-> receivedData[msg.seq + 1], seq |-> (msg.seq + 1) - 1 ] \in msgsData
          BY <2>1 DEF Lemma4
    <2>3. (msg.seq + 1) - 1 = msg.seq BY <2>seq
    <2> QED
      <3> WITNESS [ payload |-> receivedData[msg.seq + 1], seq |-> (msg.seq + 1) - 1 ] \in msgsData
      <3> QED BY <2>3
  <1>dat. DataInv
    <2>ss. senderSeq \in Nat /\ receiverSeq \in Nat BY DEF TypeOK
    <2>fS. sentData \in [1..senderSeq -> PAYLOADS] BY DEF TypeOK
    <2>fR. receivedData \in [1..receiverSeq -> PAYLOADS] BY DEF TypeOK
    <2>domR. DOMAIN receivedData = 1..receiverSeq BY <2>fR
    <2>domS. DOMAIN sentData = 1..senderSeq BY <2>fS
    <2>lenS. Len(sentData) = senderSeq BY DEF Lemma2
    <2>img. msgsData = { [ payload |-> sentData[i], seq |-> i - 1 ] : i \in 1..senderSeq }
          BY MsgsDataIsImage
    <2>rle. receiverSeq = senderSeq \/ receiverSeq = senderSeq - 1
          BY DEF CounterInv
    \* On the shared domain 1..receiverSeq, receivedData and sentData agree.
    <2>eq. \A i \in 1..receiverSeq : receivedData[i] = sentData[i]
      <3> SUFFICES ASSUME NEW i \in 1..receiverSeq PROVE receivedData[i] = sentData[i]
            OBVIOUS
      <3>1. [ payload |-> receivedData[i], seq |-> i - 1 ] \in msgsData
            BY <2>domR DEF Lemma4
      <3>2. [ payload |-> receivedData[i], seq |-> i - 1 ] \in
              { [ payload |-> sentData[j], seq |-> j - 1 ] : j \in 1..senderSeq }
            BY <3>1, <2>img
      <3>3. PICK j \in 1..senderSeq :
              [ payload |-> receivedData[i], seq |-> i - 1 ]
                = [ payload |-> sentData[j], seq |-> j - 1 ]
            BY <3>2
      <3>4. receivedData[i] = sentData[j] /\ i - 1 = j - 1
            BY <3>3
      <3>5. i = j BY <3>4
      <3> QED BY <3>4, <3>5
    <2>A. CASE receiverSeq = senderSeq
      <3>1. DOMAIN receivedData = DOMAIN sentData BY <2>domR, <2>domS, <2>A
      <3>2. \A i \in DOMAIN receivedData : receivedData[i] = sentData[i]
            BY <2>eq, <2>A, <2>domR
      <3>3. receivedData = sentData
            BY <2>fR, <2>fS, <3>1, <3>2
      <3> QED BY <3>3 DEF DataInv
    <2>B. CASE receiverSeq = senderSeq - 1
      <3> DEFINE ss == SubSeq(sentData, 1, Len(sentData) - 1)
      <3>n. Len(sentData) - 1 = receiverSeq BY <2>lenS, <2>B, <2>ss
      <3>elem. \A i \in 1 .. (Len(sentData) - 1) : sentData[i] \in PAYLOADS
            BY <2>fS, <2>lenS, <2>ss
      <3>props. /\ ss \in Seq(PAYLOADS)
                /\ Len(ss) = IF 1 <= Len(sentData) - 1 THEN (Len(sentData) - 1) - 1 + 1 ELSE 0
                /\ \A i \in 1 .. (Len(sentData) - 1) - 1 + 1 : ss[i] = sentData[1 + i - 1]
            BY <3>elem, <2>lenS, <2>ss, SubSeqPrefixProps
      <3>len. Len(ss) = receiverSeq BY <3>props, <3>n, <2>ss
      <3>dom. DOMAIN ss = 1..receiverSeq
            BY <3>props, <3>len, LenProperties
      <3>val. \A i \in 1..receiverSeq : ss[i] = sentData[i]
        <4>1. \A i \in 1 .. (Len(sentData) - 1) - 1 + 1 : ss[i] = sentData[1 + i - 1]
              BY <3>props
        <4>2. (Len(sentData) - 1) - 1 + 1 = receiverSeq BY <3>n, <2>ss
        <4> QED BY <4>1, <4>2
      <3>4. receivedData = ss
            BY <2>fR, <2>domR, <3>props, <3>dom, <3>val, <2>eq
      <3> QED BY <3>4 DEF DataInv
    <2> QED BY <2>rle, <2>A, <2>B
  <1> QED
        BY <1>cnt, <1>dat, <1>ack DEF AllInv

\*****************************************************************************
\* SAFETY. `AllInv` holds in every reachable state: it is invariant over the
\* full specification. Standard inductive-invariant argument -- base case
\* (InitInd), inductive step lifted to [Next]_vars (NextInd for the Next case,
\* plus the stutter case), and the implication (ImpliesAllInv) -- combined by
\* propositional temporal logic.
\*****************************************************************************
THEOREM Safety == Spec => []AllInv
  <1>1. Init => TypedIndInv
        BY InitInd
  <1>2. TypedIndInv /\ [Next]_vars => TypedIndInv'
    <2>1. CASE Next
          BY <2>1, NextInd
    <2>2. CASE UNCHANGED vars
          BY <2>2 DEF vars, TypedIndInv, TypeOK, IndInv, CounterInv,
                        Lemma2, Lemma3, Lemma4, Lemma5
    <2> QED BY <2>1, <2>2
  <1>3. TypedIndInv => AllInv
        BY ImpliesAllInv
  <1> QED
        BY <1>1, <1>2, <1>3, PTL DEF Spec

=========================================================