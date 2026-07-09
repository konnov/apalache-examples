----------------- MODULE ack_refines_ack_spec -----------------
EXTENDS Integers, Sequences, TLAPS

CONSTANTS
    \* The set of payloads that can be sent in every message.
    \* @type: Set(Str);
    PAYLOADS,
    \* @type: Int;
    MAX_SEQ

\* variables of ack.tla
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

L == INSTANCE ack

H == INSTANCE ack_spec
     WITH PAYLOADS <- PAYLOADS,
          sentData <- sentData,
          receivedData <- receivedData

THEOREM ack_init_refines_ack_spec_init ==
    L!Init => H!Init

THEOREM ack_next_refines_ack_spec_next ==
    L!Next => H!Next

THEOREM ack_fairness_refines_ack_spec_fairness ==
    L!Fairness => H!Fairness

THEOREM ack_refines_ack_spec ==
    L!Spec => H!Spec
<1>1. L!Init => H!Init
    BY ack_init_refines_ack_spec_init
<1>2. [L!Next]_<<sentData, receivedData>> => [H!Next]_<<sentData, receivedData>>
    BY ack_next_refines_ack_spec_next
<1>3. QED
  BY <1>1, <1>2, PTL DEF L!Spec, H!Spec


===============================================================