------------------ MODULE ack_proofs ------------------
EXTENDS ack

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

=========================================================