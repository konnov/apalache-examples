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
 * Both `SendData` actions are guarded by the MAX_SEQ bound (senderSeq < MAX_SEQ
 * in ack, Len(sentData) < MAX_SEQ in ack_spec), so the send action is DISABLED
 * at the bound and the weak-fairness conditions are satisfiable: both fair specs
 * have genuine behaviors (TLC confirms non-vacuity). This enables the FAIRNESS
 * refinement. We prove the ReceiveData half here:
 *
 *   - RecvWF : Spec => WF_hvars(H!ReceiveData)
 *
 * built from ENABLED expansions (RecvEnabledLo/RecvEnabledHi, via the
 * ExpandENABLED pragma), the enabled/step correspondences (RecvL2/RecvL1), and
 * a PTL glue step. The SendData half (WF_hvars(H!SendData)) needs a two-step
 * ReceiveAck->SendData leadsto and is not yet done, so the full `Spec => H!Spec`
 * (with H!Fairness) is not yet assembled.
 *
 * Verify with:  cd ack && tlapm -I . ack_refines_ack_spec.tla
 *
 * Igor Konnov, Claude Opus 4.8, July 2026
 *)
EXTENDS ack_proofs

\* The high-level spec, instantiated with the identity refinement mapping.
H == INSTANCE ack_spec
     WITH PAYLOADS <- PAYLOADS,
          MAX_SEQ <- MAX_SEQ,
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
    <2>pre. senderSeq = senderAck /\ senderSeq < MAX_SEQ BY DEF SendData
    <2>req. receiverSeq = senderSeq BY <2>pre, <2>ss DEF CounterInv
    <2>lenS. Len(sentData) = senderSeq BY DEF Lemma2
    <2>lenR. Len(receivedData) = receiverSeq BY DEF Lemma4
    <2>eqlen. Len(receivedData) = Len(sentData) BY <2>req, <2>lenS, <2>lenR
    <2>lbnd. Len(sentData) < MAX_SEQ BY <2>pre, <2>lenS
    <2>snd. sentData' = Append(sentData, p) /\ receivedData' = receivedData
          BY DEF SendData
    <2>hsend. H!SendData
      <3> SUFFICES \E payload \in PAYLOADS :
                     /\ Len(receivedData) = Len(sentData)
                     /\ Len(sentData) < MAX_SEQ
                     /\ sentData' = Append(sentData, payload)
                     /\ receivedData' = receivedData
            BY DEF H!SendData
      <3> WITNESS p \in PAYLOADS
      <3> QED BY <2>eqlen, <2>lbnd, <2>snd
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

\*****************************************************************************
\* FAIRNESS REFINEMENT (ReceiveData). Spec => WF_hvars(H!ReceiveData).
\* The high-level ReceiveData weak-fairness is implemented by the low-level
\* ReceiveDataClosed weak-fairness. The correspondence is 1-1: under the
\* inductive invariant, H!ReceiveData is enabled iff ReceiveDataClosed is
\* (both iff receiverSeq < senderSeq), and a low receive step is a high receive
\* step. ENABLED is expanded with the ExpandENABLED pragma; the construction of
\* the low-level enabledness witness is isolated in helper lemmas (RecvPulled)
\* to keep it out of any ENABLED-bearing context. The temporal glue is PTL.
\*****************************************************************************
LEMMA RecvPulled ==
  ASSUME TypeOK, NEW m \in msgsData, m.seq = receiverSeq
  PROVE  \E sp, rp, rqp, ssp, mdp, map, sap :
             /\ mdp = msgsData /\ ssp = senderSeq /\ sap = senderAck /\ sp = sentData
             /\ rqp = receiverSeq + 1
             /\ \E msg \in msgsData :
                  /\ msg.seq = receiverSeq
                  /\ map = msgsAck \cup { [seq |-> msg.seq] }
                  /\ rp = Append(receivedData, msg.payload)
             /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                   /\ rqp = receiverSeq /\ sp = sentData /\ rp = receivedData )
  <1>ar. receiverSeq + 1 # receiverSeq BY DEF TypeOK
  <1> WITNESS sentData, Append(receivedData, m.payload), receiverSeq + 1, senderSeq,
              msgsData, msgsAck \cup {[seq |-> m.seq]}, senderAck
  <1>1. \E msg \in msgsData :
              /\ msg.seq = receiverSeq
              /\ msgsAck \cup { [seq |-> m.seq] } = msgsAck \cup { [seq |-> msg.seq] }
              /\ Append(receivedData, m.payload) = Append(receivedData, msg.payload)
    <2> WITNESS m \in msgsData
    <2> QED OBVIOUS
  <1> QED BY <1>1, <1>ar

LEMMA RecvEnabledLo ==
  ASSUME TypeOK
  PROVE  ENABLED <<ReceiveDataClosed>>_vars <=> (\E m \in msgsData : m.seq = receiverSeq)
  <1>bwd. (\E m \in msgsData : m.seq = receiverSeq) =>
            \E sp, rp, rqp, ssp, mdp, map, sap :
               /\ \E msg \in msgsData :
                    /\ msg.seq = receiverSeq
                    /\ map = msgsAck \cup { [seq |-> msg.seq] }
                    /\ rqp = receiverSeq + 1
                    /\ rp = Append(receivedData, msg.payload)
                    /\ mdp = msgsData /\ ssp = senderSeq /\ sap = senderAck /\ sp = sentData
               /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                     /\ rqp = receiverSeq /\ sp = sentData /\ rp = receivedData )
    <2> SUFFICES ASSUME NEW m \in msgsData, m.seq = receiverSeq
                 PROVE  \E sp, rp, rqp, ssp, mdp, map, sap :
               /\ \E msg \in msgsData :
                    /\ msg.seq = receiverSeq
                    /\ map = msgsAck \cup { [seq |-> msg.seq] }
                    /\ rqp = receiverSeq + 1
                    /\ rp = Append(receivedData, msg.payload)
                    /\ mdp = msgsData /\ ssp = senderSeq /\ sap = senderAck /\ sp = sentData
               /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                     /\ rqp = receiverSeq /\ sp = sentData /\ rp = receivedData )
          OBVIOUS
    <2>p. \E sp, rp, rqp, ssp, mdp, map, sap :
             /\ mdp = msgsData /\ ssp = senderSeq /\ sap = senderAck /\ sp = sentData
             /\ rqp = receiverSeq + 1
             /\ \E msg \in msgsData :
                  /\ msg.seq = receiverSeq
                  /\ map = msgsAck \cup { [seq |-> msg.seq] }
                  /\ rp = Append(receivedData, msg.payload)
             /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                   /\ rqp = receiverSeq /\ sp = sentData /\ rp = receivedData )
          BY RecvPulled
    <2> QED BY <2>p, Zenon
  <1>fwd. ( \E sp, rp, rqp, ssp, mdp, map, sap :
               /\ \E msg \in msgsData :
                    /\ msg.seq = receiverSeq
                    /\ map = msgsAck \cup { [seq |-> msg.seq] }
                    /\ rqp = receiverSeq + 1
                    /\ rp = Append(receivedData, msg.payload)
                    /\ mdp = msgsData /\ ssp = senderSeq /\ sap = senderAck /\ sp = sentData
               /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                     /\ rqp = receiverSeq /\ sp = sentData /\ rp = receivedData ) ) => (\E m \in msgsData : m.seq = receiverSeq)
          BY Zenon
  <1>exp. ENABLED <<ReceiveDataClosed>>_vars <=>
            \E sp, rp, rqp, ssp, mdp, map, sap :
               /\ \E msg \in msgsData :
                    /\ msg.seq = receiverSeq
                    /\ map = msgsAck \cup { [seq |-> msg.seq] }
                    /\ rqp = receiverSeq + 1
                    /\ rp = Append(receivedData, msg.payload)
                    /\ mdp = msgsData /\ ssp = senderSeq /\ sap = senderAck /\ sp = sentData
               /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                     /\ rqp = receiverSeq /\ sp = sentData /\ rp = receivedData )
          BY ExpandENABLED, Isa DEF ReceiveDataClosed, ReceiveData, vars
  <1> QED BY <1>bwd, <1>fwd, <1>exp

LEMMA RecvEnabledHi ==
  ASSUME TypeOK
  PROVE  ENABLED <<H!ReceiveData>>_hvars <=> (Len(receivedData) < Len(sentData))
  <1>seqR. receivedData \in Seq(PAYLOADS) BY SeqDef DEF TypeOK
  <1>bwd. (Len(receivedData) < Len(sentData)) =>
            \E sdp, rdp :
               /\ Len(receivedData) < Len(sentData)
               /\ rdp = Append(receivedData, sentData[Len(receivedData) + 1])
               /\ sdp = sentData
               /\ ~( /\ sdp = sentData /\ rdp = receivedData )
    <2> SUFFICES ASSUME Len(receivedData) < Len(sentData)
                 PROVE  \E sdp, rdp :
                           /\ Len(receivedData) < Len(sentData)
                           /\ rdp = Append(receivedData, sentData[Len(receivedData) + 1])
                           /\ sdp = sentData
                           /\ ~( /\ sdp = sentData /\ rdp = receivedData )
          OBVIOUS
    <2> DEFINE e == sentData[Len(receivedData) + 1]
    <2>len. Len(Append(receivedData, e)) = Len(receivedData) + 1 BY <1>seqR, AppendProperties
    <2>lenN. Len(receivedData) \in Nat BY <1>seqR, LenProperties
    <2>neq. Append(receivedData, e) # receivedData BY <2>len, <2>lenN
    <2> WITNESS sentData, Append(receivedData, e)
    <2> QED BY <2>neq
  <1>fwd. ( \E sdp, rdp :
               /\ Len(receivedData) < Len(sentData)
               /\ rdp = Append(receivedData, sentData[Len(receivedData) + 1])
               /\ sdp = sentData
               /\ ~( /\ sdp = sentData /\ rdp = receivedData ) )
          => (Len(receivedData) < Len(sentData)) BY Zenon
  <1>exp. ENABLED <<H!ReceiveData>>_hvars <=>
            \E sdp, rdp :
               /\ Len(receivedData) < Len(sentData)
               /\ rdp = Append(receivedData, sentData[Len(receivedData) + 1])
               /\ sdp = sentData
               /\ ~( /\ sdp = sentData /\ rdp = receivedData )
          BY ExpandENABLED, Isa DEF H!ReceiveData, hvars
  <1> QED BY <1>bwd, <1>fwd, <1>exp

LEMMA RecvL2 ==
  ASSUME TypeOK, Lemma2, Lemma3, Lemma4,
         ENABLED <<H!ReceiveData>>_hvars
  PROVE  ENABLED <<ReceiveDataClosed>>_vars
  <1>1. Len(receivedData) < Len(sentData) BY RecvEnabledHi
  <1>ss. senderSeq \in Nat /\ receiverSeq \in Nat BY DEF TypeOK
  <1>2. receiverSeq < senderSeq
        <2>a. Len(sentData) = senderSeq BY DEF Lemma2
        <2>b. Len(receivedData) = receiverSeq BY DEF Lemma4
        <2> QED BY <1>1, <2>a, <2>b
  <1>img. msgsData = { [ payload |-> sentData[i], seq |-> i - 1 ] : i \in 1..senderSeq }
        BY MsgsDataIsImage
  <1>3. [ payload |-> sentData[receiverSeq + 1], seq |-> receiverSeq ] \in msgsData
        <2>a. receiverSeq + 1 \in 1..senderSeq BY <1>2, <1>ss
        <2>b. (receiverSeq + 1) - 1 = receiverSeq BY <1>ss
        <2> QED BY <1>img, <2>a, <2>b
  <1>4. \E m \in msgsData : m.seq = receiverSeq
        <2> WITNESS [ payload |-> sentData[receiverSeq + 1], seq |-> receiverSeq ] \in msgsData
        <2> QED BY <1>3
  <1> QED BY <1>4, RecvEnabledLo


LEMMA RecvL1 ==
  ASSUME TypeOK, Lemma2, Lemma3, Lemma4, <<ReceiveDataClosed>>_vars
  PROVE  <<H!ReceiveData>>_hvars
  <1>rdc. ReceiveDataClosed BY DEF vars
  <1> PICK msg \in msgsData : ReceiveData(msg) BY <1>rdc DEF ReceiveDataClosed
  <1> USE DEF ReceiveData
  <1>ss. senderSeq \in Nat /\ receiverSeq \in Nat BY DEF TypeOK
  <1>msgT. msg \in [ payload: PAYLOADS, seq: Nat ] BY DEF TypeOK
  <1>pre. msg.seq = receiverSeq BY DEF ReceiveData
  <1>lenS. Len(sentData) = senderSeq BY DEF Lemma2
  <1>lenR. Len(receivedData) = receiverSeq BY DEF Lemma4
  <1>bnd. msg.seq < senderSeq BY MsgsDataSeqBound
  <1>lt. Len(receivedData) < Len(sentData) BY <1>bnd, <1>pre, <1>lenS, <1>lenR
  <1>img. msgsData = { [ payload |-> sentData[i], seq |-> i - 1 ] : i \in 1..senderSeq }
        BY MsgsDataIsImage
  <1>pick. PICK i \in 1..senderSeq : msg = [ payload |-> sentData[i], seq |-> i - 1 ] BY <1>img
  <1>iv. i - 1 = receiverSeq BY <1>pick, <1>pre
  <1>ival. i = receiverSeq + 1 BY <1>iv, <1>ss
  <1>payl. msg.payload = sentData[receiverSeq + 1] BY <1>pick, <1>ival
  <1>recv. receivedData' = Append(receivedData, msg.payload) /\ sentData' = sentData BY DEF ReceiveData
  <1>match. receivedData' = Append(receivedData, sentData[Len(receivedData) + 1]) BY <1>recv, <1>payl, <1>lenR
  <1>hrd. H!ReceiveData BY <1>lt, <1>match, <1>recv DEF H!ReceiveData
  <1>neq. hvars' # hvars
    <2>seqR. receivedData \in Seq(PAYLOADS) BY SeqDef DEF TypeOK
    <2>pay. msg.payload \in PAYLOADS BY <1>msgT
    <2>len. Len(receivedData') = Len(receivedData) + 1 BY <1>recv, <2>seqR, <2>pay, AppendProperties
    <2>lenN. Len(receivedData) \in Nat BY <2>seqR, LenProperties
    <2>rneq. receivedData' # receivedData BY <2>len, <2>lenN
    <2> QED BY <2>rneq DEF hvars
  <1> QED BY <1>hrd, <1>neq DEF hvars

THEOREM RecvWF == Spec => WF_hvars(H!ReceiveData)
  <1>inv. Spec => []TypedIndInv
    <2>1. Init => TypedIndInv BY InitInd
    <2>2. TypedIndInv /\ [Next]_vars => TypedIndInv'
      <3>1. CASE Next BY <3>1, NextInd
      <3>2. CASE UNCHANGED vars
            BY <3>2 DEF vars, TypedIndInv, TypeOK, IndInv, CounterInv, Lemma2, Lemma3, Lemma4, Lemma5
      <3> QED BY <3>1, <3>2
    <2> QED BY <2>1, <2>2, PTL DEF Spec
  <1>wf. Spec => WF_vars(ReceiveDataClosed) BY DEF Spec, Fairness
  <1>L1. TypedIndInv /\ <<ReceiveDataClosed>>_vars => <<H!ReceiveData>>_hvars
        BY RecvL1 DEF TypedIndInv, IndInv
  <1>L2. TypedIndInv /\ ENABLED <<H!ReceiveData>>_hvars => ENABLED <<ReceiveDataClosed>>_vars
        BY RecvL2 DEF TypedIndInv, IndInv
  <1> QED BY <1>inv, <1>wf, <1>L1, <1>L2, PTL


===============================================================
