------------------------- MODULE MC_n11t2f2_inductive -----------------------------
EXTENDS Integers, typedefs

N == 11
T == 2
F == 2
CORRECT == {
    "0_OF_REPLICA", "1_OF_REPLICA", "2_OF_REPLICA", "3_OF_REPLICA",
    "4_OF_REPLICA", "5_OF_REPLICA", "6_OF_REPLICA", "7_OF_REPLICA",
    "8_OF_REPLICA"
}
FAULTY == { "9_OF_REPLICA", "10_OF_REPLICA" }
ROUNDS == 1..2

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

INSTANCE Ben_or83_inductive

\* Isolate Lemma8a for the inductive-step check.
Inv8 == Lemma8_Q2RequiresNoQuorumFaster

\* Step2-only transition, to target the Lemma8 Step2 admit specifically.
NextS2 == \E id \in CORRECT: Step2(id)
======================================================================================
