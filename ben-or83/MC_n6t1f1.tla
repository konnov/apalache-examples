---------------------------------- MODULE MC_n6t1f1 ----------------------------------
EXTENDS Integers, typedefs

N == 6
T == 1
F == 1
CORRECT == {
    "0_OF_REPLICA", "1_OF_REPLICA", "2_OF_REPLICA", "3_OF_REPLICA", "4_OF_REPLICA"
}
FAULTY == {"5_OF_REPLICA"}
ROUNDS == 1..3

VARIABLES
  \* The current value by a replica, called $x_P$ in the paper.
  \* @type: REPLICA -> Int;
  value,
  \* The decision by a replica, where -1 means no decision.
  \* @type: REPLICA -> Int;
  decision,
  \* The round number of a replica, called $r$ in the paper.
  \* @type: REPLICA -> Int;
  round,
  \* The replica step: S1, S2, S3.
  \* @type: REPLICA -> STEP;
  step,
  \* Type-1 messages sent by the correct and faulty replicas, mapped by rounds.
  \* @type: Int -> Set($msgOne);
  msgs1,
  \* Type-2 messages sent by the correct and faulty replicas, mapped by rounds.
  \* @type: Int -> Set($msgTwo);
  msgs2

INSTANCE Ben_or83
======================================================================================