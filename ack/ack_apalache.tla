------------------ MODULE ack_apalache ------------------
(*
  Checking inductiveness with Apalache:
  
  1. apalache-mc check --config=ack.cfg \
    --length=0 --inv=AllInv --next=Next --init=IndInvInit ack.tla
  2. apalache-mc check --config=ack.cfg \
    --length=0 --inv=IndInv --next=Next --init=Init ack.tla
  3. apalache-mc check --config=ack.cfg \
    --length=1 --inv=IndInv --next=Next --init=IndInvInit ack.tla
 *)
EXTENDS Apalache, ack

ApalacheInit ==
    /\ senderSeq \in 0..MAX_SEQ
    /\ senderAck \in 0..MAX_SEQ
    /\ receiverSeq \in 0..MAX_SEQ
    /\ LET \* @type: Seq(Str);
         seq == Gen(MAX_SEQ)
       IN
       /\ \A i \in DOMAIN seq: seq[i] \in PAYLOADS
       /\ sentData = seq
    /\ LET \* @type: Seq(Str);
         seq == Gen(MAX_SEQ)
       IN
       /\ \A i \in DOMAIN seq: seq[i] \in PAYLOADS
       /\ receivedData = seq
    /\ msgsAck \in SUBSET [seq: 0..MAX_SEQ]
    /\ IsFiniteSet(msgsAck)
    /\ msgsData \in SUBSET [payload: PAYLOADS, seq: 0..MAX_SEQ]
    /\ IsFiniteSet(msgsData)

IndInvInit ==
    ApalacheInit /\ IndInv

=========================================================