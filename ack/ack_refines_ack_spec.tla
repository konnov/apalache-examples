----------------- MODULE ack_refines_ack_spec -----------------
(*
 * Safety refinement: the low-level protocol `ack` implements the SAFETY part of
 * the high-level specification `ack_spec`, under the identity refinement mapping
 * on (sentData, receivedData). We prove:
 *
 *   - ack_init_refines_ack_spec_init : Init => H!Init
 *   - ack_next_refines_ack_spec_next : TypedIndInv /\ Next => [H!Next]_hvars
 *   - ack_refines_ack_spec           : Spec => H!Init /\ [][H!Next]_hvars
 *
 * The step refinement needs ack's inductive invariant `TypedIndInv` (proved in
 * ack_proofs): at a SendData the two histories have equal length, and a received
 * message's payload matches the corresponding position of `sentData`. Every
 * ReceiveAck / MAX_SEQ-stutter low-level step leaves (sentData, receivedData)
 * unchanged, so it is a high-level stuttering step.
 *
 * NOTE on fairness. We deliberately do NOT prove `Spec => H!Spec` with the
 * high-level fairness. `Fairness` imposes weak fairness on the bare
 * `SendDataClosed` action, which stays ENABLED at senderSeq = MAX_SEQ (only
 * Next's `BoundedCounters'` blocks the step). Weak fairness then demands a step
 * that [Next]_vars cannot take, so the fair `Spec` has no behaviors (it is
 * vacuous) for finite MAX_SEQ. Only the safety refinement is meaningful here.
 *
 * Verify with:  cd ack && tlapm -I . ack_refines_ack_spec.tla
 *
 * Igor Konnov, Claude Opus 4.8, July 2026
 *)
EXTENDS ack_proofs

\* The high-level spec, instantiated with the identity refinement mapping.
H == INSTANCE ack_spec
     WITH PAYLOADS <- PAYLOADS,
          sentData <- sentData,
          receivedData <- receivedData

\* The high-level variables (= H!vars under the identity mapping).
hvars == << sentData, receivedData >>

\*****************************************************************************
\* INIT. The low-level initial condition establishes the high-level one.
\*****************************************************************************
THEOREM ack_init_refines_ack_spec_init == Init => H!Init
  BY DEF Init, H!Init

\*****************************************************************************
\* NEXT (step refinement). Under the inductive invariant, every low-level Next
\* step either is a high-level Next step or leaves (sentData, receivedData)
\* unchanged (a high-level stuttering step).
\*****************************************************************************
THEOREM ack_next_refines_ack_spec_next ==
    TypedIndInv /\ Next => [H!Next]_hvars
  <1> SUFFICES ASSUME TypedIndInv, Next PROVE [H!Next]_hvars
        OBVIOUS
  <1> USE DEF TypedIndInv, IndInv
  <1>d. \/ SendDataClosed \/ ReceiveDataClosed \/ ReceiveAckClosed
        \/ UNCHANGED vars
        BY DEF Next
  \* ===== SendData: refines high-level SendData =====
  <1>1. CASE SendDataClosed
    <2> PICK p \in PAYLOADS : SendData(p)
          BY <1>1 DEF SendDataClosed
    <2> USE DEF SendData
    <2>ss. senderSeq \in Nat /\ senderAck \in Nat /\ receiverSeq \in Nat
          BY DEF TypeOK
    <2>pre. senderSeq = senderAck BY DEF SendData
    <2>req. receiverSeq = senderSeq BY <2>pre, <2>ss DEF CounterInv
    <2>lenS. Len(sentData) = senderSeq BY DEF Lemma2
    <2>lenR. Len(receivedData) = receiverSeq BY DEF Lemma4
    <2>eqlen. Len(receivedData) = Len(sentData) BY <2>req, <2>lenS, <2>lenR
    <2>snd. sentData' = Append(sentData, p) /\ receivedData' = receivedData
          BY DEF SendData
    <2>hsend. H!SendData
      <3> SUFFICES \E payload \in PAYLOADS :
                     /\ Len(receivedData) = Len(sentData)
                     /\ sentData' = Append(sentData, payload)
                     /\ receivedData' = receivedData
            BY DEF H!SendData
      <3> WITNESS p \in PAYLOADS
      <3> QED BY <2>eqlen, <2>snd
    <2> QED BY <2>hsend DEF H!Next
  \* ===== ReceiveData: refines high-level ReceiveData =====
  <1>2. CASE ReceiveDataClosed
    <2> PICK msg \in msgsData : ReceiveData(msg)
          BY <1>2 DEF ReceiveDataClosed
    <2> USE DEF ReceiveData
    <2>ss. senderSeq \in Nat /\ receiverSeq \in Nat BY DEF TypeOK
    <2>pre. msg.seq = receiverSeq BY DEF ReceiveData
    <2>lenS. Len(sentData) = senderSeq BY DEF Lemma2
    <2>lenR. Len(receivedData) = receiverSeq BY DEF Lemma4
    <2>bnd. msg.seq < senderSeq BY MsgsDataSeqBound
    <2>lt. Len(receivedData) < Len(sentData) BY <2>bnd, <2>pre, <2>lenS, <2>lenR
    <2>img. msgsData = { [ payload |-> sentData[i], seq |-> i - 1 ] : i \in 1..senderSeq }
          BY MsgsDataIsImage
    <2>pick. PICK i \in 1..senderSeq : msg = [ payload |-> sentData[i], seq |-> i - 1 ]
          BY <2>img
    <2>iv. i - 1 = receiverSeq BY <2>pick, <2>pre
    <2>ival. i = receiverSeq + 1 BY <2>iv, <2>ss
    <2>payl. msg.payload = sentData[receiverSeq + 1] BY <2>pick, <2>ival
    <2>recv. receivedData' = Append(receivedData, msg.payload) /\ sentData' = sentData
          BY DEF ReceiveData
    <2>match. receivedData' = Append(receivedData, sentData[Len(receivedData) + 1])
          BY <2>recv, <2>payl, <2>lenR
    <2>hrecv. H!ReceiveData BY <2>lt, <2>match, <2>recv DEF H!ReceiveData
    <2> QED BY <2>hrecv DEF H!Next
  \* ===== ReceiveAck: high-level stuttering =====
  <1>3. CASE ReceiveAckClosed
    <2> PICK msg \in msgsAck : ReceiveAck(msg)
          BY <1>3 DEF ReceiveAckClosed
    <2>unch. sentData' = sentData /\ receivedData' = receivedData
          BY DEF ReceiveAck
    <2> QED BY <2>unch DEF hvars
  \* ===== MAX_SEQ stutter: high-level stuttering =====
  <1>4. CASE UNCHANGED vars
    <2>unch. sentData' = sentData /\ receivedData' = receivedData
          BY <1>4 DEF vars
    <2> QED BY <2>unch DEF hvars
  <1> QED BY <1>d, <1>1, <1>2, <1>3, <1>4

\*****************************************************************************
\* SAFETY REFINEMENT. `Spec` refines the safety part of the high-level spec:
\* the high-level initial condition holds and every step is [H!Next]_hvars.
\* Standard inductive-invariant lifting: base case (InitInd), the inductive
\* step (NextInd, plus the stutter case) to carry `TypedIndInv`, and the step
\* refinement above, combined by propositional temporal logic.
\*****************************************************************************
THEOREM ack_refines_ack_spec == Spec => H!Init /\ [][H!Next]_hvars
  <1>1. Init => H!Init
        BY ack_init_refines_ack_spec_init
  <1>2. Init => TypedIndInv
        BY InitInd
  <1>3. TypedIndInv /\ [Next]_vars => TypedIndInv'
    <2> SUFFICES ASSUME TypedIndInv, [Next]_vars PROVE TypedIndInv'
          OBVIOUS
    <2>1. CASE Next
          BY <2>1, NextInd
    <2>2. CASE UNCHANGED vars
          BY <2>2 DEF vars, TypedIndInv, TypeOK, IndInv, CounterInv,
                        Lemma2, Lemma3, Lemma4, Lemma5
    <2> QED BY <2>1, <2>2
  <1>4. TypedIndInv /\ [Next]_vars => [H!Next]_hvars
    <2> SUFFICES ASSUME TypedIndInv, [Next]_vars PROVE [H!Next]_hvars
          OBVIOUS
    <2>1. CASE Next
          BY <2>1, ack_next_refines_ack_spec_next
    <2>2. CASE UNCHANGED vars
          BY <2>2 DEF vars, hvars
    <2> QED BY <2>1, <2>2
  <1> QED
        BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec

===============================================================
