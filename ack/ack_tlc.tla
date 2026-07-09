------------------ MODULE ack_tlc ------------------
\* Special version for TLC.
EXTENDS ack

TLCTypeOK ==
    /\ senderSeq \in 0..MAX_SEQ
    /\ senderAck \in 0..MAX_SEQ
    /\ receiverSeq \in 0..MAX_SEQ
    /\ sentData \in [1..senderSeq -> PAYLOADS]
    /\ receivedData \in [1..receiverSeq -> PAYLOADS]
    /\ msgsAck \in SUBSET [seq: 0..MAX_SEQ]
    /\ IsFiniteSet(msgsAck)
    /\ msgsData \in SUBSET [payload: PAYLOADS, seq: 0..MAX_SEQ]
    /\ IsFiniteSet(msgsData)

\* The initialization predicate combined with the inductive invariant.
IndInvInit ==
    /\ TLCTypeOK
    /\ IndInv

=========================================================