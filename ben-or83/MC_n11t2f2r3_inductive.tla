------------------------- MODULE MC_n11t2f2r3_inductive -----------------------------
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
ROUNDS == 1..3

VARIABLES
  \* @type: REPLICA -> Int;
  value,
  \* @type: REPLICA -> Int;
  decision,
  \* @type: REPLICA -> Int;
  round,
  \* @type: REPLICA -> STEP;
  step,
  \* @type: Int -> Set($msgOne);
  msgs1,
  \* @type: Int -> Set($msgTwo);
  msgs2

INSTANCE Ben_or83_inductive

\* Isolate Lemma1c for the inductive-step check.
Inv1 == Lemma1_DecisionRequiresLastQuorumLessRam

\* Step3-only transition, to target the Lemma1 Step3 admit specifically.
NextS3 == \E id \in CORRECT: Step3(id)
======================================================================================
