---------------------------- MODULE ack ----------------------------
(*
  A simple send-acknowledgment protocol. This protocol uses sequence numbers to
  ensure that the messages are delivered in order and without duplication.
  
  This specification is designed to be used with the three TLA+ tools: (1) the
  model checker TLC, (2) the symbolic model checker Apalache, and (3) the proof
  system TLAPS.
  
  Check the specialized modules in ack_tlc.tla, ack_apalache.tla, and
  ack_proofs.tla.
 *)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    \* The set of payloads that can be sent in every message.
    \* @type: Set(Str);
    PAYLOADS,
    \* The maximum sequence number that can be used in the protocol.
    \* @type: Int;
    MAX_SEQ

\* This is the high-level view of the protocol:
\*
\* Sender ----> Data (payload, N) -----> Receiver
\* Sender <---------- Ack (N) <--------- Receiver

VARIABLES
    \* All data messages that are sent by the sender to the receiver.
    \* Each message comes with a payload and a sequence number.
    \* @type: Set({ payload: Str, seq: Int });
    msgsData,
    \* All acknowledgment messages that are sent by the receiver to the sender.
    \* Each acknowledgment comes with a sequence number.
    \* @type: Set({ seq: Int });
    msgsAck,
    \* The current sequence number of the sender.
    \* This number is incremented every time the sender sends a new data message.
    \* @type: Int;
    senderSeq,
    \* The sequence number of the last acknowledgment received by the sender.
    \* @type: Int;
    senderAck,
    \* The current sequence number on the receiver's side.
    \* @type: Int;
    receiverSeq,
    \* The history of the data sent by the sender, in the order they were sent.
    \* @type: Seq(Str);
    sentData,
    \* The history of the data received by the receiver, in the order they were
    \* received.
    \* @type: Seq(Str);
    receivedData

\* All variables in the state machine, needed to define temporal properties.
vars == << msgsData, msgsAck, senderSeq, senderAck, receiverSeq, sentData, receivedData >>

\* Constraint on the counters.
BoundedCounters ==
    /\ senderSeq \in 0..MAX_SEQ
    /\ senderAck \in 0..MAX_SEQ
    /\ receiverSeq \in 0..MAX_SEQ

\* Protocol initialization.
Init ==
    /\ msgsData = {}
    /\ msgsAck = {}
    /\ senderSeq = 0
    /\ senderAck = 0
    /\ receiverSeq = 0
    /\ sentData = << >>
    /\ receivedData = << >>

\* The sender sends a data message with the given payload and the current
\* sequence number.  This is possible only if the sender has received an
\* acknowledgment for the previous message.
SendData(payload) ==
    /\ senderSeq = senderAck
    /\ msgsData' = msgsData \cup { [payload |-> payload, seq |-> senderSeq] }
    /\ senderSeq' = senderSeq + 1
    /\ sentData' = Append(sentData, payload)
    /\ UNCHANGED <<msgsAck, receiverSeq, senderAck, receivedData>>

\* The receiver receives a data message with the given payload and the current
\* sequence number. The receiver also sends an acknowledgment for the received
\* message.
\*
\* @type: { payload: Str, seq: Int } => Bool;
ReceiveData(msg) ==
    /\ msg.seq = receiverSeq
    /\ msgsAck' = msgsAck \cup { [seq |-> msg.seq] }
    /\ receiverSeq' = receiverSeq + 1
    /\ receivedData' = Append(receivedData, msg.payload)
    /\ UNCHANGED <<msgsData, senderSeq, senderAck, sentData>>

\* The sender receives an acknowledgment for the latest data message it has
\* sent.  This lets the sender to progress with the next data message.
\*
\* @type: { seq: Int } => Bool;
ReceiveAck(msg) ==
    /\ msg.seq = senderAck
    /\ senderAck' = senderAck + 1
    /\ UNCHANGED <<msgsData, msgsAck, senderSeq, receiverSeq, sentData, receivedData>>

\* ReceiveData with its own choice of the parameter.
ReceiveDataClosed ==
    \E msg \in msgsData:
        ReceiveData(msg)

\* SendData with its own choice of the parameter.
SendDataClosed ==
    \E payload \in PAYLOADS:
        SendData(payload)

\* ReceiveAck with its own choice of the parameter.
ReceiveAckClosed ==
    \E msg \in msgsAck:
        ReceiveAck(msg)

\* The next-state transition relation of the protocol.
Next ==
    /\ \/ SendDataClosed
       \/ ReceiveDataClosed
       \/ ReceiveAckClosed
       \/ /\ UNCHANGED vars
          /\ senderAck = MAX_SEQ
          /\ senderSeq = MAX_SEQ
          /\ receiverSeq = MAX_SEQ
    \* Bound the values of the counters to avoid infinite state space.
    \* NOTE: This leads to a deadlock when the counters are exhausted.
    \* We could add stuttering for this case.
    /\ BoundedCounters'

\* The fairness constraints of the protocol.
Fairness ==
    /\ WF_vars(SendDataClosed)
    /\ WF_vars(ReceiveDataClosed)
    /\ WF_vars(ReceiveAckClosed)

\* The restriction of the protocol with Next and Fairness.
Spec ==
    Init /\ [][Next]_vars /\ Fairness
    
\* A key state invariant on the counters
CounterInv ==
    /\ senderSeq \in { senderAck, senderAck + 1 }    
    /\ receiverSeq \in { senderSeq, senderSeq - 1 }
    /\ senderAck \in { receiverSeq, receiverSeq - 1 }

\* An action invariant on the counters, which shows that the counter do not
\* decrease.
CounterMono ==
    \/ /\ senderSeq' = senderSeq + 1
       /\ UNCHANGED <<senderAck, receiverSeq>>
    \/ /\ senderAck' = senderAck + 1
       /\ UNCHANGED <<senderSeq, receiverSeq>>
    \/ /\ receiverSeq' = receiverSeq + 1
       /\ UNCHANGED <<senderSeq, senderAck>>

\* The invariant on the data sent and received.
DataInv ==
    \/ receivedData = sentData
    \/ receivedData = SubSeq(sentData, 1, Len(sentData) - 1)

\* For every acknowledgment sent, the corresponding data message has been sent.
AckInv ==
    \A msg \in msgsAck:
        \E msg2 \in msgsData:
            msg.seq = msg2.seq

\* All state invariants combined.
AllInv ==
    /\ CounterInv
    /\ DataInv
    /\ AckInv

\* Our temporal expectation about message delivery.
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

\* Every message that is sent is eventually received by the receiver.
EventualDelivery ==
    []<>(receivedData = sentData)

\* A lemma for our inductive invariant.
Lemma2 ==
    /\ Cardinality(msgsData) = senderSeq 
    /\ Len(sentData) = senderSeq

\* A lemma for our inductive invariant.
Lemma3 ==
    \A i \in DOMAIN sentData:
        [ payload |-> sentData[i], seq |-> i - 1 ] \in msgsData

\* A lemma for our inductive invariant.
Lemma4 ==
    /\ \A i \in DOMAIN receivedData:
        [ payload |-> receivedData[i], seq |-> i - 1 ] \in msgsData
    /\ Len(receivedData) = receiverSeq

\* A lemma for our inductive invariant.
Lemma5 ==
    /\ \A i \in DOMAIN receivedData:
        [ seq |-> i - 1 ] \in msgsAck
    /\ { m.seq + 1: m \in msgsAck } = DOMAIN receivedData

\* Our inductive invariant. It is used to show protocol safety (AllInv) in
\* one step. We use Apalache to check that this invariant is inductive on
\* bounded data structures. Further, we use TLAPS to prove that the protocol is
\* safe for all choices of the parameters PAYLOADS and MAX_SEQ.
IndInv ==
    /\ CounterInv
    /\ Lemma2
    /\ Lemma3
    /\ Lemma4
    /\ Lemma5

====================================================================