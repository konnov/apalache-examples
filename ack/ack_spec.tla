------------------------ MODULE ack_spec ------------------------
EXTENDS Integers, Sequences

CONSTANTS
    \* The set of payloads that can be sent in every message.
    \* @type: Set(Str);
    PAYLOADS,
    \* The maximum number of messages that can be sent in the protocol.
    \* @type: Int;
    MAX_SEQ

VARIABLES
    \* The history of the data sent by the sender, in the order they were sent.
    \* @type: Seq(Str);
    sentData,
    \* The history of the data received by the receiver, in the order they were
    \* received.
    \* @type: Seq(Str);
    receivedData

vars == << sentData, receivedData >>

Init ==
    /\ sentData = << >>
    /\ receivedData = << >>

SendData ==
    \E payload \in PAYLOADS:
        /\ Len(receivedData) = Len(sentData)
        \* Guard the send by the bound (mirrors ack.tla), so this action is
        \* DISABLED once MAX_SEQ messages have been sent: WF_vars(SendData) stays
        \* satisfiable and the fair Spec is not vacuous.
        /\ Len(sentData) < MAX_SEQ
        /\ sentData' = Append(sentData, payload)
        /\ UNCHANGED receivedData

ReceiveData ==
    /\ Len(receivedData) < Len(sentData)
    /\ LET data == sentData[Len(receivedData) + 1] IN
        /\ receivedData' = Append(receivedData, data)
        /\ UNCHANGED sentData

Next ==
    \/ SendData
    \/ ReceiveData
    \* Explicit stuttering once the bound is reached (mirrors ack.tla): avoids a
    \* deadlock when both histories have length MAX_SEQ.
    \/ /\ UNCHANGED vars
       /\ Len(sentData) = MAX_SEQ
       /\ Len(receivedData) = MAX_SEQ

\* The invariant on the data sent and received.
DataInv ==
    \/ receivedData = sentData
    \/ receivedData = SubSeq(sentData, 1, Len(sentData) - 1)

\* Every message that is sent is eventually received by the receiver.
EventualDelivery ==
    []<>(receivedData = sentData)

\* The fairness constraints of the protocol.
Fairness ==
    /\ WF_vars(SendData)
    /\ WF_vars(ReceiveData)

\* The restriction of the protocol with Next and Fairness.
Spec ==
    Init /\ [][Next]_vars /\ Fairness
=================================================================