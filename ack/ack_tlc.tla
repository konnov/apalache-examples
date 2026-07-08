------------------ MODULE ack_tlc ------------------
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

IndInvInit ==
    /\ TLCTypeOK
    /\ IndInv

=========================================================