----------------- MODULE ack_refines_ack_spec -----------------
(*
 * Refinement: the low-level protocol `ack` implements the high-level
 * specification `ack_spec`, under the identity refinement mapping on
 * (sentData, receivedData). The refinement is COMPLETE -- safety AND fairness,
 * with no OMITTED steps and no assumptions:
 *
 *   - ack_init_refines_ack_spec_init : Init => H!Init
 *   - ack_next_refines_ack_spec_next : TypedIndInv /\ Next => [H!Next]_hvars
 *   - ack_refines_ack_spec           : Spec => H!Init /\ [][H!Next]_hvars  (safety)
 *   - RecvWF                         : Spec => WF_hvars(H!ReceiveData)
 *   - SendWF                         : Spec => WF_hvars(H!SendData)
 *   - ack_refines_ack_spec_fair      : Spec => H!Spec                      (full)
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
 * have genuine behaviors (TLC confirms non-vacuity).
 *
 * The fairness refinement expands ENABLED with the ExpandENABLED pragma (the
 * witness constructions are isolated in *Pulled helpers, kept out of any
 * ENABLED-bearing context), establishes the enabled/step correspondences under
 * the invariant, and glues everything with PTL. ReceiveData is a 1-1
 * correspondence (pure PTL); SendData is a two-step ReceiveAck->SendData leadsto
 * (SendLA via WF(ReceiveAck), SendLB via WF(SendData)) because when an ack is
 * pending the high-level send is enabled while the low-level send is not.
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


\*****************************************************************************
\* FAIRNESS REFINEMENT (SendData). Spec => WF_hvars(H!SendData).
\* Harder than ReceiveData: the enabledness is NOT 1-1. When the two histories
\* are equal but an ack is still pending (senderAck = senderSeq - 1), the
\* high-level SendData is enabled but the low-level SendDataClosed is not; the
\* low-level ReceiveAckClosed is, and firing it (WF) makes senderAck = senderSeq,
\* after which SendDataClosed is enabled and fires (WF). So it is a two-step
\* leadsto (SendLA via WF(ReceiveAck); SendLB via WF(SendData)), chained and
\* lifted to WF by PTL. EHS is the invariant-characterization of the high-level
\* send-enabledness (cleaner to prime than ENABLED).
\*****************************************************************************

\* ===== SendDataClosed enabledness =====
LEMMA SendPulled ==
  ASSUME TypeOK, senderSeq = senderAck, senderSeq < MAX_SEQ, NEW p \in PAYLOADS
  PROVE  \E sdp, rdp, rqp, ssp, mdp, map, sap :
            /\ senderSeq = senderAck
            /\ senderSeq < MAX_SEQ
            /\ ssp = senderSeq + 1
            /\ rdp = receivedData /\ rqp = receiverSeq /\ map = msgsAck /\ sap = senderAck
            /\ \E payload \in PAYLOADS :
                 /\ mdp = msgsData \cup {[payload |-> payload, seq |-> senderSeq]}
                 /\ sdp = Append(sentData, payload)
            /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                  /\ rqp = receiverSeq /\ sdp = sentData /\ rdp = receivedData )
  <1>ar. senderSeq + 1 # senderSeq BY DEF TypeOK
  <1> WITNESS Append(sentData, p), receivedData, receiverSeq, senderSeq + 1,
              msgsData \cup {[payload |-> p, seq |-> senderSeq]}, msgsAck, senderAck
  <1>1. \E payload \in PAYLOADS :
                 /\ msgsData \cup {[payload |-> p, seq |-> senderSeq]}
                      = msgsData \cup {[payload |-> payload, seq |-> senderSeq]}
                 /\ Append(sentData, p) = Append(sentData, payload)
    <2> WITNESS p \in PAYLOADS
    <2> QED OBVIOUS
  <1> QED BY <1>1, <1>ar

LEMMA SendEnabledLo ==
  ASSUME TypeOK
  PROVE  ENABLED <<SendDataClosed>>_vars <=>
           (senderSeq = senderAck /\ senderSeq < MAX_SEQ /\ PAYLOADS # {})
  <1>bwd. (senderSeq = senderAck /\ senderSeq < MAX_SEQ /\ PAYLOADS # {}) =>
            \E sdp, rdp, rqp, ssp, mdp, map, sap :
               /\ \E payload \in PAYLOADS :
                    /\ senderSeq = senderAck
                    /\ senderSeq < MAX_SEQ
                    /\ mdp = msgsData \cup {[payload |-> payload, seq |-> senderSeq]}
                    /\ ssp = senderSeq + 1
                    /\ sdp = Append(sentData, payload)
                    /\ map = msgsAck /\ rqp = receiverSeq /\ sap = senderAck /\ rdp = receivedData
               /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                     /\ rqp = receiverSeq /\ sdp = sentData /\ rdp = receivedData )
    <2> SUFFICES ASSUME senderSeq = senderAck, senderSeq < MAX_SEQ, PAYLOADS # {}
                 PROVE  \E sdp, rdp, rqp, ssp, mdp, map, sap :
               /\ \E payload \in PAYLOADS :
                    /\ senderSeq = senderAck
                    /\ senderSeq < MAX_SEQ
                    /\ mdp = msgsData \cup {[payload |-> payload, seq |-> senderSeq]}
                    /\ ssp = senderSeq + 1
                    /\ sdp = Append(sentData, payload)
                    /\ map = msgsAck /\ rqp = receiverSeq /\ sap = senderAck /\ rdp = receivedData
               /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                     /\ rqp = receiverSeq /\ sdp = sentData /\ rdp = receivedData )
          OBVIOUS
    <2> PICK p \in PAYLOADS : TRUE OBVIOUS
    <2> QED BY SendPulled, Zenon
  <1>fwd. ( \E sdp, rdp, rqp, ssp, mdp, map, sap :
               /\ \E payload \in PAYLOADS :
                    /\ senderSeq = senderAck
                    /\ senderSeq < MAX_SEQ
                    /\ mdp = msgsData \cup {[payload |-> payload, seq |-> senderSeq]}
                    /\ ssp = senderSeq + 1
                    /\ sdp = Append(sentData, payload)
                    /\ map = msgsAck /\ rqp = receiverSeq /\ sap = senderAck /\ rdp = receivedData
               /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                     /\ rqp = receiverSeq /\ sdp = sentData /\ rdp = receivedData ) )
          => (senderSeq = senderAck /\ senderSeq < MAX_SEQ /\ PAYLOADS # {})
          BY Zenon
  <1>exp. ENABLED <<SendDataClosed>>_vars <=>
            \E sdp, rdp, rqp, ssp, mdp, map, sap :
               /\ \E payload \in PAYLOADS :
                    /\ senderSeq = senderAck
                    /\ senderSeq < MAX_SEQ
                    /\ mdp = msgsData \cup {[payload |-> payload, seq |-> senderSeq]}
                    /\ ssp = senderSeq + 1
                    /\ sdp = Append(sentData, payload)
                    /\ map = msgsAck /\ rqp = receiverSeq /\ sap = senderAck /\ rdp = receivedData
               /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                     /\ rqp = receiverSeq /\ sdp = sentData /\ rdp = receivedData )
          BY ExpandENABLED, Isa DEF SendDataClosed, SendData, vars
  <1> QED BY <1>bwd, <1>fwd, <1>exp

\* ===== ReceiveAckClosed enabledness =====
LEMMA AckPulled ==
  ASSUME TypeOK, NEW mm \in msgsAck, mm.seq = senderAck
  PROVE  \E sdp, rdp, rqp, ssp, mdp, map, sap :
            /\ sap = senderAck + 1
            /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ rqp = receiverSeq
            /\ sdp = sentData /\ rdp = receivedData
            /\ \E msg \in msgsAck : msg.seq = senderAck
            /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                  /\ rqp = receiverSeq /\ sdp = sentData /\ rdp = receivedData )
  <1>ar. senderAck + 1 # senderAck BY DEF TypeOK
  <1> WITNESS sentData, receivedData, receiverSeq, senderSeq, msgsData, msgsAck, senderAck + 1
  <1>1. \E msg \in msgsAck : msg.seq = senderAck
    <2> WITNESS mm \in msgsAck
    <2> QED OBVIOUS
  <1> QED BY <1>1, <1>ar

LEMMA AckEnabledLo ==
  ASSUME TypeOK
  PROVE  ENABLED <<ReceiveAckClosed>>_vars <=> (\E m \in msgsAck : m.seq = senderAck)
  <1>bwd. (\E m \in msgsAck : m.seq = senderAck) =>
            \E sdp, rdp, rqp, ssp, mdp, map, sap :
               /\ \E msg \in msgsAck :
                    /\ msg.seq = senderAck
                    /\ sap = senderAck + 1
                    /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ rqp = receiverSeq
                    /\ sdp = sentData /\ rdp = receivedData
               /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                     /\ rqp = receiverSeq /\ sdp = sentData /\ rdp = receivedData )
    <2> SUFFICES ASSUME NEW mm \in msgsAck, mm.seq = senderAck
                 PROVE  \E sdp, rdp, rqp, ssp, mdp, map, sap :
               /\ \E msg \in msgsAck :
                    /\ msg.seq = senderAck
                    /\ sap = senderAck + 1
                    /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ rqp = receiverSeq
                    /\ sdp = sentData /\ rdp = receivedData
               /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                     /\ rqp = receiverSeq /\ sdp = sentData /\ rdp = receivedData )
          OBVIOUS
    <2> QED BY AckPulled, Zenon
  <1>fwd. ( \E sdp, rdp, rqp, ssp, mdp, map, sap :
               /\ \E msg \in msgsAck :
                    /\ msg.seq = senderAck
                    /\ sap = senderAck + 1
                    /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ rqp = receiverSeq
                    /\ sdp = sentData /\ rdp = receivedData
               /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                     /\ rqp = receiverSeq /\ sdp = sentData /\ rdp = receivedData ) )
          => (\E m \in msgsAck : m.seq = senderAck)
          BY Zenon
  <1>exp. ENABLED <<ReceiveAckClosed>>_vars <=>
            \E sdp, rdp, rqp, ssp, mdp, map, sap :
               /\ \E msg \in msgsAck :
                    /\ msg.seq = senderAck
                    /\ sap = senderAck + 1
                    /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ rqp = receiverSeq
                    /\ sdp = sentData /\ rdp = receivedData
               /\ ~( /\ mdp = msgsData /\ map = msgsAck /\ ssp = senderSeq /\ sap = senderAck
                     /\ rqp = receiverSeq /\ sdp = sentData /\ rdp = receivedData )
          BY ExpandENABLED, Isa DEF ReceiveAckClosed, ReceiveAck, vars
  <1> QED BY <1>bwd, <1>fwd, <1>exp

\* ===== H!SendData enabledness =====
LEMMA SendHiPulled ==
  ASSUME TypeOK, Len(receivedData) = Len(sentData), Len(sentData) < MAX_SEQ, NEW p \in PAYLOADS
  PROVE  \E sdp, rdp :
            /\ Len(receivedData) = Len(sentData)
            /\ Len(sentData) < MAX_SEQ
            /\ rdp = receivedData
            /\ \E payload \in PAYLOADS : sdp = Append(sentData, payload)
            /\ ~( /\ sdp = sentData /\ rdp = receivedData )
  <1>seqS. sentData \in Seq(PAYLOADS) BY SeqDef DEF TypeOK
  <1>len. Len(Append(sentData, p)) = Len(sentData) + 1 BY <1>seqS, AppendProperties
  <1>lenN. Len(sentData) \in Nat BY <1>seqS, LenProperties
  <1>neq. Append(sentData, p) # sentData BY <1>len, <1>lenN
  <1> WITNESS Append(sentData, p), receivedData
  <1>1. \E payload \in PAYLOADS : Append(sentData, p) = Append(sentData, payload)
    <2> WITNESS p \in PAYLOADS
    <2> QED OBVIOUS
  <1> QED BY <1>1, <1>neq

LEMMA SendEnabledHi ==
  ASSUME TypeOK
  PROVE  ENABLED <<H!SendData>>_hvars <=>
           (Len(receivedData) = Len(sentData) /\ Len(sentData) < MAX_SEQ /\ PAYLOADS # {})
  <1>bwd. (Len(receivedData) = Len(sentData) /\ Len(sentData) < MAX_SEQ /\ PAYLOADS # {}) =>
            \E sdp, rdp :
               /\ \E payload \in PAYLOADS :
                    /\ Len(receivedData) = Len(sentData)
                    /\ Len(sentData) < MAX_SEQ
                    /\ sdp = Append(sentData, payload)
                    /\ rdp = receivedData
               /\ ~( /\ sdp = sentData /\ rdp = receivedData )
    <2> SUFFICES ASSUME Len(receivedData) = Len(sentData), Len(sentData) < MAX_SEQ, PAYLOADS # {}
                 PROVE  \E sdp, rdp :
               /\ \E payload \in PAYLOADS :
                    /\ Len(receivedData) = Len(sentData)
                    /\ Len(sentData) < MAX_SEQ
                    /\ sdp = Append(sentData, payload)
                    /\ rdp = receivedData
               /\ ~( /\ sdp = sentData /\ rdp = receivedData )
          OBVIOUS
    <2> PICK p \in PAYLOADS : TRUE OBVIOUS
    <2> QED BY SendHiPulled, Zenon
  <1>fwd. ( \E sdp, rdp :
               /\ \E payload \in PAYLOADS :
                    /\ Len(receivedData) = Len(sentData)
                    /\ Len(sentData) < MAX_SEQ
                    /\ sdp = Append(sentData, payload)
                    /\ rdp = receivedData
               /\ ~( /\ sdp = sentData /\ rdp = receivedData ) )
          => (Len(receivedData) = Len(sentData) /\ Len(sentData) < MAX_SEQ /\ PAYLOADS # {})
          BY Zenon
  <1>exp. ENABLED <<H!SendData>>_hvars <=>
            \E sdp, rdp :
               /\ \E payload \in PAYLOADS :
                    /\ Len(receivedData) = Len(sentData)
                    /\ Len(sentData) < MAX_SEQ
                    /\ sdp = Append(sentData, payload)
                    /\ rdp = receivedData
               /\ ~( /\ sdp = sentData /\ rdp = receivedData )
          BY ExpandENABLED, Isa DEF H!SendData, hvars
  <1> QED BY <1>bwd, <1>fwd, <1>exp


\* ===== state-level correspondences (used by the leadsto) =====
LEMMA SL_SDC ==
  ASSUME TypeOK, senderSeq = senderAck, senderSeq < MAX_SEQ, PAYLOADS # {}
  PROVE  ENABLED <<SendDataClosed>>_vars
  BY SendEnabledLo

LEMMA SL_HSD ==
  ASSUME TypeOK, Lemma2, Lemma4, ENABLED <<H!SendData>>_hvars
  PROVE  senderSeq < MAX_SEQ /\ receiverSeq = senderSeq /\ PAYLOADS # {}
  <1>1. Len(receivedData) = Len(sentData) /\ Len(sentData) < MAX_SEQ /\ PAYLOADS # {}
        BY SendEnabledHi
  <1>2. Len(sentData) = senderSeq BY DEF Lemma2
  <1>3. Len(receivedData) = receiverSeq BY DEF Lemma4
  <1> QED BY <1>1, <1>2, <1>3

LEMMA SL_RAC ==
  ASSUME TypeOK, Lemma5, senderAck < receiverSeq
  PROVE  ENABLED <<ReceiveAckClosed>>_vars
  <1>ss. senderAck \in Nat /\ receiverSeq \in Nat BY DEF TypeOK
  <1>fR. receivedData \in [1..receiverSeq -> PAYLOADS] BY DEF TypeOK
  <1>dom. DOMAIN receivedData = 1..receiverSeq BY <1>fR
  <1>1. senderAck + 1 \in 1..receiverSeq BY <1>ss
  <1>2. senderAck + 1 \in DOMAIN receivedData BY <1>1, <1>dom
  <1>3. [ seq |-> (senderAck + 1) - 1 ] \in msgsAck BY <1>2 DEF Lemma5
  <1>4. [ seq |-> (senderAck + 1) - 1 ] = [ seq |-> senderAck ] BY <1>ss
  <1>5. [ seq |-> senderAck ] \in msgsAck BY <1>3, <1>4
  <1>6. \E m \in msgsAck : m.seq = senderAck
    <2> WITNESS [ seq |-> senderAck ] \in msgsAck
    <2> QED BY <1>5
  <1> QED BY <1>6, AckEnabledLo

LEMMA SL_step ==
  ASSUME TypeOK, CounterInv, Lemma2, Lemma3, Lemma4, <<SendDataClosed>>_vars
  PROVE  <<H!SendData>>_hvars
  <1>sdc. SendDataClosed BY DEF vars
  <1> PICK p \in PAYLOADS : SendData(p) BY <1>sdc DEF SendDataClosed
  <1> USE DEF SendData
  <1>ss. senderSeq \in Nat /\ senderAck \in Nat /\ receiverSeq \in Nat BY DEF TypeOK
  <1>pre. senderSeq = senderAck /\ senderSeq < MAX_SEQ BY DEF SendData
  <1>req. receiverSeq = senderSeq BY <1>pre, <1>ss DEF CounterInv
  <1>lenS. Len(sentData) = senderSeq BY DEF Lemma2
  <1>lenR. Len(receivedData) = receiverSeq BY DEF Lemma4
  <1>eqlen. Len(receivedData) = Len(sentData) BY <1>req, <1>lenS, <1>lenR
  <1>lbnd. Len(sentData) < MAX_SEQ BY <1>pre, <1>lenS
  <1>snd. sentData' = Append(sentData, p) /\ receivedData' = receivedData BY DEF SendData
  <1>hsd. H!SendData
    <2> SUFFICES \E payload \in PAYLOADS :
                   /\ Len(receivedData) = Len(sentData)
                   /\ Len(sentData) < MAX_SEQ
                   /\ sentData' = Append(sentData, payload)
                   /\ receivedData' = receivedData
          BY DEF H!SendData
    <2> WITNESS p \in PAYLOADS
    <2> QED BY <1>eqlen, <1>lbnd, <1>snd
  <1>neq. hvars' # hvars
    <2>seqS. sentData \in Seq(PAYLOADS) BY SeqDef DEF TypeOK
    <2>len. Len(sentData') = Len(sentData) + 1 BY <1>snd, <2>seqS, AppendProperties
    <2>lenN. Len(sentData) \in Nat BY <2>seqS, LenProperties
    <2>sneq. sentData' # sentData BY <2>len, <2>lenN
    <2> QED BY <2>sneq DEF hvars
  <1> QED BY <1>hsd, <1>neq DEF hvars


\* EHS: the invariant-characterization of ENABLED <<H!SendData>>_hvars.
EHS == senderSeq < MAX_SEQ /\ receiverSeq = senderSeq /\ PAYLOADS # {}

LEMMA EHS_iff ==
  ASSUME TypeOK, Lemma2, Lemma4
  PROVE  ENABLED <<H!SendData>>_hvars <=> EHS
  <1>1. Len(sentData) = senderSeq BY DEF Lemma2
  <1>2. Len(receivedData) = receiverSeq BY DEF Lemma4
  <1>3. ENABLED <<H!SendData>>_hvars <=>
          (Len(receivedData) = Len(sentData) /\ Len(sentData) < MAX_SEQ /\ PAYLOADS # {})
        BY SendEnabledHi
  <1> QED BY <1>1, <1>2, <1>3 DEF EHS

\* RAC leadsto: pending ack resolves.
LEMMA SendLA ==
  Spec => ( (EHS /\ senderSeq # senderAck) ~> (EHS /\ senderSeq = senderAck) )
  <1>inv. Spec => []TypedIndInv
    <2>1. Init => TypedIndInv BY InitInd
    <2>2. TypedIndInv /\ [Next]_vars => TypedIndInv'
      <3>1. CASE Next BY <3>1, NextInd
      <3>2. CASE UNCHANGED vars
            BY <3>2 DEF vars, TypedIndInv, TypeOK, IndInv, CounterInv, Lemma2, Lemma3, Lemma4, Lemma5
      <3> QED BY <3>1, <3>2
    <2> QED BY <2>1, <2>2, PTL DEF Spec
  <1>wf. Spec => WF_vars(ReceiveAckClosed) BY DEF Spec, Fairness
  <1>nx. Spec => [][Next]_vars BY DEF Spec
  <1>en. TypedIndInv /\ EHS /\ senderSeq # senderAck => ENABLED <<ReceiveAckClosed>>_vars
    <2> SUFFICES ASSUME TypedIndInv, EHS, senderSeq # senderAck
                 PROVE  ENABLED <<ReceiveAckClosed>>_vars
          OBVIOUS
    <2>ss. senderSeq \in Nat /\ senderAck \in Nat /\ receiverSeq \in Nat BY DEF TypedIndInv, TypeOK
    <2>ci. senderAck \in {receiverSeq, receiverSeq - 1} BY DEF TypedIndInv, IndInv, CounterInv
    <2>eq. receiverSeq = senderSeq BY DEF EHS
    <2>lt. senderAck < receiverSeq BY <2>ss, <2>ci, <2>eq
    <2> QED BY <2>lt, SL_RAC DEF TypedIndInv, IndInv
  <1>st. TypedIndInv /\ EHS /\ senderSeq # senderAck /\ <<ReceiveAckClosed>>_vars
           => (EHS /\ senderSeq = senderAck)'
    <2> SUFFICES ASSUME TypedIndInv, EHS, senderSeq # senderAck, <<ReceiveAckClosed>>_vars
                 PROVE  (EHS /\ senderSeq = senderAck)'
          OBVIOUS
    <2>rac. ReceiveAckClosed BY DEF vars
    <2> PICK msg \in msgsAck : ReceiveAck(msg) BY <2>rac DEF ReceiveAckClosed
    <2>ss. senderSeq \in Nat /\ senderAck \in Nat /\ receiverSeq \in Nat BY DEF TypedIndInv, TypeOK
    <2>ci. senderAck \in {receiverSeq, receiverSeq - 1} BY DEF TypedIndInv, IndInv, CounterInv
    <2>eq. receiverSeq = senderSeq BY DEF EHS
    <2>lt. senderAck = senderSeq - 1 BY <2>ss, <2>ci, <2>eq
    <2>fr. senderAck' = senderAck + 1 /\ senderSeq' = senderSeq /\ receiverSeq' = receiverSeq
          BY DEF ReceiveAck
    <2>eqp. senderSeq' = senderAck' BY <2>fr, <2>lt, <2>ss
    <2>ehsp. EHS' BY <2>fr, <2>eq DEF EHS
    <2> QED BY <2>eqp, <2>ehsp
  <1>pe. TypedIndInv /\ TypedIndInv' /\ EHS /\ senderSeq # senderAck /\ [Next]_vars
           => (EHS /\ senderSeq # senderAck)' \/ (EHS /\ senderSeq = senderAck)'
    <2> SUFFICES ASSUME TypedIndInv, TypedIndInv', EHS, senderSeq # senderAck, [Next]_vars
                 PROVE  (EHS /\ senderSeq # senderAck)' \/ (EHS /\ senderSeq = senderAck)'
          OBVIOUS
    <2>ss. senderSeq \in Nat /\ senderAck \in Nat /\ receiverSeq \in Nat BY DEF TypedIndInv, TypeOK
    <2>eq. receiverSeq = senderSeq BY DEF EHS
    <2>d. \/ SendDataClosed \/ ReceiveDataClosed \/ ReceiveAckClosed \/ UNCHANGED vars
          BY DEF Next
    <2>1. CASE SendDataClosed
      <3> PICK p \in PAYLOADS : SendData(p) BY <2>1 DEF SendDataClosed
      <3> QED BY <2>1 DEF SendData  \* senderSeq = senderAck contradicts senderSeq # senderAck
    <2>2. CASE ReceiveDataClosed
      <3> PICK msg \in msgsData : ReceiveData(msg) BY <2>2 DEF ReceiveDataClosed
      <3>mt. msg.seq < senderSeq BY MsgsDataSeqBound DEF TypedIndInv, IndInv
      <3>me. msg.seq = receiverSeq BY DEF ReceiveData
      <3> QED BY <3>mt, <3>me, <2>eq  \* receiverSeq < senderSeq contradicts receiverSeq = senderSeq
    <2>3. CASE ReceiveAckClosed
      <3>0. <<ReceiveAckClosed>>_vars
        <4> PICK msg \in msgsAck : ReceiveAck(msg) BY <2>3 DEF ReceiveAckClosed
        <4>ss. senderAck \in Nat BY DEF TypedIndInv, TypeOK
        <4>fr. senderAck' = senderAck + 1 BY DEF ReceiveAck
        <4>neq. vars' # vars BY <4>fr, <4>ss DEF vars
        <4> QED BY <2>3, <4>neq
      <3>1. (EHS /\ senderSeq = senderAck)' BY <3>0, <1>st
      <3> QED BY <3>1
    <2>4. CASE UNCHANGED vars
      <3>1. (EHS /\ senderSeq # senderAck)'
            BY <2>4, <2>ss DEF vars, EHS
      <3> QED BY <3>1
    <2> QED BY <2>d, <2>1, <2>2, <2>3, <2>4
  <1> QED BY <1>inv, <1>wf, <1>nx, <1>en, <1>st, <1>pe, PTL

\* SDC leadsto: once the ack has caught up, a send fires.
LEMMA SendLB ==
  Spec => ( (EHS /\ senderSeq = senderAck) ~> <<SendDataClosed>>_vars )
  <1>inv. Spec => []TypedIndInv
    <2>1. Init => TypedIndInv BY InitInd
    <2>2. TypedIndInv /\ [Next]_vars => TypedIndInv'
      <3>1. CASE Next BY <3>1, NextInd
      <3>2. CASE UNCHANGED vars
            BY <3>2 DEF vars, TypedIndInv, TypeOK, IndInv, CounterInv, Lemma2, Lemma3, Lemma4, Lemma5
      <3> QED BY <3>1, <3>2
    <2> QED BY <2>1, <2>2, PTL DEF Spec
  <1>wf. Spec => WF_vars(SendDataClosed) BY DEF Spec, Fairness
  <1>nx. Spec => [][Next]_vars BY DEF Spec
  <1>en. TypedIndInv /\ EHS /\ senderSeq = senderAck => ENABLED <<SendDataClosed>>_vars
    <2> SUFFICES ASSUME TypedIndInv, EHS, senderSeq = senderAck
                 PROVE  ENABLED <<SendDataClosed>>_vars
          OBVIOUS
    <2>1. senderSeq < MAX_SEQ /\ PAYLOADS # {} BY DEF EHS
    <2> QED BY <2>1, SL_SDC DEF TypedIndInv, IndInv
  <1>pe. TypedIndInv /\ TypedIndInv' /\ EHS /\ senderSeq = senderAck /\ [Next]_vars
           => (EHS /\ senderSeq = senderAck)' \/ <<SendDataClosed>>_vars
    <2> SUFFICES ASSUME TypedIndInv, TypedIndInv', EHS, senderSeq = senderAck, [Next]_vars
                 PROVE  (EHS /\ senderSeq = senderAck)' \/ <<SendDataClosed>>_vars
          OBVIOUS
    <2>ss. senderSeq \in Nat /\ senderAck \in Nat /\ receiverSeq \in Nat BY DEF TypedIndInv, TypeOK
    <2>eq. receiverSeq = senderSeq BY DEF EHS
    <2>d. \/ SendDataClosed \/ ReceiveDataClosed \/ ReceiveAckClosed \/ UNCHANGED vars
          BY DEF Next
    <2>1. CASE SendDataClosed
      <3> PICK p \in PAYLOADS : SendData(p) BY <2>1 DEF SendDataClosed
      <3>fr. senderSeq' = senderSeq + 1 BY DEF SendData
      <3>neq. vars' # vars BY <3>fr, <2>ss DEF vars
      <3> QED BY <2>1, <3>neq
    <2>2. CASE ReceiveDataClosed
      <3> PICK msg \in msgsData : ReceiveData(msg) BY <2>2 DEF ReceiveDataClosed
      <3>mt. msg.seq < senderSeq BY MsgsDataSeqBound DEF TypedIndInv, IndInv
      <3>me. msg.seq = receiverSeq BY DEF ReceiveData
      <3> QED BY <3>mt, <3>me, <2>eq
    <2>3. CASE ReceiveAckClosed
      <3> PICK msg \in msgsAck : ReceiveAck(msg) BY <2>3 DEF ReceiveAckClosed
      <3>ms. msg.seq + 1 \in 1..receiverSeq BY MsgsAckSeqBound DEF TypedIndInv, IndInv
      <3>mp. msg.seq = senderAck BY DEF ReceiveAck
      \* senderAck = senderSeq = receiverSeq, but msg.seq = senderAck and msg.seq+1 <= receiverSeq => senderAck < receiverSeq
      <3> QED BY <3>ms, <3>mp, <2>ss, <2>eq
    <2>4. CASE UNCHANGED vars
      <3>1. (EHS /\ senderSeq = senderAck)' BY <2>4, <2>ss DEF vars, EHS
      <3> QED BY <3>1
    <2> QED BY <2>d, <2>1, <2>2, <2>3, <2>4
  <1> QED BY <1>inv, <1>wf, <1>nx, <1>en, <1>pe, PTL

THEOREM SendWF == Spec => WF_hvars(H!SendData)
  <1>inv. Spec => []TypedIndInv
    <2>1. Init => TypedIndInv BY InitInd
    <2>2. TypedIndInv /\ [Next]_vars => TypedIndInv'
      <3>1. CASE Next BY <3>1, NextInd
      <3>2. CASE UNCHANGED vars
            BY <3>2 DEF vars, TypedIndInv, TypeOK, IndInv, CounterInv, Lemma2, Lemma3, Lemma4, Lemma5
      <3> QED BY <3>1, <3>2
    <2> QED BY <2>1, <2>2, PTL DEF Spec
  <1>iff. Spec => [](ENABLED <<H!SendData>>_hvars <=> EHS)
    <2>1. TypedIndInv => (ENABLED <<H!SendData>>_hvars <=> EHS)
          BY EHS_iff DEF TypedIndInv, IndInv
    <2> QED BY <1>inv, <2>1, PTL
  <1>step. [](TypedIndInv /\ <<SendDataClosed>>_vars => <<H!SendData>>_hvars)
    <2>1. TypedIndInv /\ <<SendDataClosed>>_vars => <<H!SendData>>_hvars
          BY SL_step DEF TypedIndInv, IndInv
    <2> QED BY <2>1, PTL
  <1>la. Spec => ( (EHS /\ senderSeq # senderAck) ~> (EHS /\ senderSeq = senderAck) ) BY SendLA
  <1>lb. Spec => ( (EHS /\ senderSeq = senderAck) ~> <<SendDataClosed>>_vars ) BY SendLB
  <1>t1. Spec => ( (EHS /\ senderSeq # senderAck) ~> <<SendDataClosed>>_vars )
        BY <1>la, <1>lb, PTL
  <1>taut. ( EHS /\ senderSeq # senderAck ) \/ ( EHS /\ senderSeq = senderAck ) <=> EHS
           OBVIOUS
  <1>c1. Spec => ( EHS ~> <<SendDataClosed>>_vars ) BY <1>t1, <1>lb, <1>taut, PTL
  <1>c2. Spec => ( EHS ~> <<H!SendData>>_hvars ) BY <1>c1, <1>inv, <1>step, PTL
  <1>c3. Spec => ( ENABLED <<H!SendData>>_hvars ~> <<H!SendData>>_hvars ) BY <1>c2, <1>iff, PTL
  <1> QED BY <1>c3, PTL

\*****************************************************************************
\* FULL FAIRNESS REFINEMENT.  refines the high-level spec including its
\* weak-fairness: Spec => H!Spec. Combines the safety refinement with both
\* weak-fairness conditions (RecvWF, SendWF) by propositional temporal logic.
\*****************************************************************************
THEOREM ack_refines_ack_spec_fair == Spec => H!Spec
  <1>1. Spec => H!Init /\ [][H!Next]_hvars BY ack_refines_ack_spec
  <1>2. Spec => WF_hvars(H!SendData) BY SendWF
  <1>3. Spec => WF_hvars(H!ReceiveData) BY RecvWF
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF H!Spec, H!Fairness, H!vars, hvars


===============================================================
