---------------------------- MODULE ack ----------------------------
(*
  A simple acknowledgment protocol.
  
  1. apalache-mc check --config=ack.cfg \
    --length=0 --inv=AllInv --next=Next --init=IndInvInit ack.tla
  2. apalache-mc check --config=ack.cfg \
    --length=0 --inv=IndInv --next=Next --init=Init ack.tla
  3. apalache-mc check --config=ack.cfg \
    --length=1 --inv=IndInv --next=Next --init=IndInvInit ack.tla
 *)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    PAYLOADS,
    \* @type: Int;
    MAX_SEQ

SENDER == "sender"
RECEIVER == "receiver"

\* Sender ----------> Data ----- >Receiver
\* Sender <---------- Ack <----- Receiver

VARIABLES
    \* @type: Set({ payload: Str, seq: Int });
    msgsData,
    \* @type: Set({ seq: Int });
    msgsAck,
    \* @type: Int;
    senderSeq,
    \* @type: Int;
    senderAck,
    \* @type: Int;
    receiverSeq,
    \* @type: Seq(Str);
    sentData,
    \* @type: Seq(Str);
    receivedData

vars == << msgsData, msgsAck, senderSeq, senderAck, receiverSeq, sentData, receivedData >>

ConstInit ==
    PAYLOADS \in SUBSET {"alice", "bob", "carol", "dave", "eve"}

BoundedCounters ==
    /\ senderSeq \in 0..MAX_SEQ
    /\ senderAck \in 0..MAX_SEQ
    /\ receiverSeq \in 0..MAX_SEQ

Init ==
    /\ msgsData = {}
    /\ msgsAck = {}
    /\ senderSeq = 0
    /\ senderAck = 0
    /\ receiverSeq = 0
    /\ sentData = << >>
    /\ receivedData = << >>

(*
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
*)

SendData(payload) ==
    /\ senderSeq = senderAck
    /\ msgsData' = msgsData \cup { [payload |-> payload, seq |-> senderSeq] }
    /\ senderSeq' = senderSeq + 1
    /\ sentData' = Append(sentData, payload)
    /\ UNCHANGED <<msgsAck, receiverSeq, senderAck, receivedData>>

\* @type: { payload: Str, seq: Int } => Bool;
ReceiveData(msg) ==
    /\ msg.seq = receiverSeq
    /\ msgsAck' = msgsAck \cup { [seq |-> msg.seq] }
    /\ receiverSeq' = receiverSeq + 1
    /\ receivedData' = Append(receivedData, msg.payload)
    /\ UNCHANGED <<msgsData, senderSeq, senderAck, sentData>>

\* @type: { seq: Int } => Bool;
ReceiveAck(msg) ==
    /\ msg.seq = senderAck
    /\ senderAck' = senderAck + 1
    /\ UNCHANGED <<msgsData, msgsAck, senderSeq, receiverSeq, sentData, receivedData>>

ReceivedDataClosed ==
    \E msg \in msgsData: ReceiveData(msg)

SendDataClosed ==
    \E payload \in PAYLOADS: SendData(payload)

ReceiveAckClosed ==
    \E msg \in msgsAck: ReceiveAck(msg)

Next ==
    /\ \/ SendDataClosed
       \/ ReceivedDataClosed
       \/ ReceiveAckClosed
    /\ BoundedCounters'

Fairness ==
    /\ WF_vars(SendDataClosed)
    /\ WF_vars(ReceivedDataClosed)
    /\ WF_vars(ReceiveAckClosed)

Spec ==
    Init /\ [][Next]_vars /\ Fairness
    
CounterInv ==
    /\ senderSeq \in { senderAck, senderAck + 1 }    
    /\ receiverSeq \in { senderSeq, senderSeq - 1 }
    /\ senderAck \in { receiverSeq, receiverSeq - 1 }
    
CounterMono ==
    \/ /\ senderSeq' = senderSeq + 1
       /\ UNCHANGED <<senderAck, receiverSeq>>
    \/ /\ senderAck' = senderAck + 1
       /\ UNCHANGED <<senderSeq, receiverSeq>>
    \/ /\ receiverSeq' = receiverSeq + 1
       /\ UNCHANGED <<senderSeq, senderAck>>

DataInv ==
    \/ receivedData = sentData
    \/ receivedData = SubSeq(sentData, 1, Len(sentData) - 1)

\* for every acknowledgment sent, the corresponding data message has been sent
AckInv ==
    \A msg \in msgsAck:
        \E msg2 \in msgsData:
            msg.seq = msg2.seq

AllInv ==
    /\ CounterInv
    /\ DataInv
    /\ AckInv

EveryMessageIsDelivered ==
    [](\A msg \in msgsData:
        <>(/\ Len(receivedData) > msg.seq
           /\ receivedData[msg.seq + 1] = msg.payload))

(*
EverySentMessageIsDelivered ==
    [](\A payload \in PAYLOADS, seqNo \in Int:
        <<(SendData(payload) /\ senderSeq = seqNo)>>_vars
            => <>(/\ Len(receivedData) > seqNo
                  /\ receivedData[seqNo + 1] = payload))
*)

EventualDelivery ==
    []<>(receivedData = sentData)

Lemma2 ==
    /\ Cardinality(msgsData) = senderSeq 
    /\ Len(sentData) = senderSeq

Lemma3 ==
    \A i \in DOMAIN sentData:
        [ payload |-> sentData[i], seq |-> i - 1 ] \in msgsData

Lemma4 ==
    /\ \A i \in DOMAIN receivedData:
        [ payload |-> receivedData[i], seq |-> i - 1 ] \in msgsData
    /\ Len(receivedData) = receiverSeq

Lemma5 ==
    /\ \A i \in DOMAIN receivedData:
        [ seq |-> i - 1 ] \in msgsAck
    /\ { m.seq + 1: m \in msgsAck } = DOMAIN receivedData

IndInv ==
    /\ CounterInv
    /\ Lemma2
    /\ Lemma3
    /\ Lemma4
    /\ Lemma5

====================================================================