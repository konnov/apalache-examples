------------------------ MODULE ack_spec ------------------------
EXTENDS Integers, Sequences

CONSTANTS
    \* The set of payloads that can be sent in every message.
    \* @type: Set(Str);
    PAYLOADS

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