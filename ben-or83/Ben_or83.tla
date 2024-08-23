--------------------------------- MODULE Ben_or83 ------------------------------------
(*
 * This is a TLA+ specification of the Ben-Or's solution to the Byzantine consensus
 * problem. The algorithm is described in the paper:
 *
 * M. Ben-Or. Another advantage of free choice (extended abstract). PODC 1983.
 *
 * The algorithm is probabilistic. We focus on safety and, therefore, abstract
 * probabilities with non-determinism.
 *
 * Igor Konnov, 2024
 *)
EXTENDS FiniteSets, Integers, typedefs

\* The set of values to choose from
VALUES == { 0, 1 }

CONSTANTS
    \* The total number of replicas.
    \* @type: Int;
    N,
    \* An upper bound on the number of faulty replicas.
    \* @type: Int;
    T,
    \* The actual number of faulty replicas (unknown to the replicas).
    \* @type: Int;
    F,
    \* The set of the correct (honest) replicas.
    \* @type: Set(REPLICA);
    CORRECT,
    \* The set of the Byzantine (faulty) replicas.
    \* @type: Set(REPLICA);
    FAULTY,
    \* The set of rounds, which we bound for model checking.
    \* @type: Set(Int);
    ROUNDS

ALL == CORRECT \union FAULTY
NO_DECISION == -1

ASSUME N > 5 * T /\ Cardinality(CORRECT) = N - F /\ Cardinality(FAULTY) = F
ASSUME 1 \in ROUNDS
ASSUME NO_DECISION \notin VALUES

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
  \* @type: Int -> Set($msgA);
  msgs1,
  \* Type-2 messages sent by the correct and faulty replicas, mapped by rounds.
  \* @type: Int -> Set($msgB);
  msgs2

Init ==
  \* non-deterministically choose the initial values
  /\ value \in [ CORRECT -> VALUES ]
  /\ round = [ r \in CORRECT |-> 1 ]
  /\ step = [ r \in CORRECT |-> S1 ]
  \* TODO: send the faulty messages right in the initial state
  /\ msgs1 = [ r \in ROUNDS |-> {}]
  /\ msgs2 = [ r \in ROUNDS |-> {}]

\* @type: REPLICA => Bool;
Step1(id) ==
  LET r == round[id] IN
  /\ step[id] = S1
  /\ msgs1' = [msgs1 EXCEPT ![r] = @ \union { M1(id, r, value[id]) }]
  /\ step' = [step EXCEPT ![id] = S2]
  /\ UNCHANGED << value, round, msgs2 >>

Step2(id) ==
  LET r == round[id] IN
  /\ step[id] = S2
  /\ \E received \in SUBSET msgs1[r]:
     /\ Cardinality(received) >= N - T
     /\ LET Weights == [ v \in VALUES |->
              Cardinality({ m \in received: m.v = v }) ]
        IN
        \/ \E v \in VALUES: 
          /\ 2 * Weights[v] > N
          /\ msgs2' = [msgs2 EXCEPT ![r] = @ \union { D2(id, r, v) }]
        \//\ \A v \in VALUES: 2 * Weights[v] <= N
          /\ msgs2' = [msgs2 EXCEPT ![r] = @ \union { Q2(id, r) }]
  /\ step' = [ step EXCEPT ![id] = S3 ]
  /\ UNCHANGED << value, round, msgs1 >>

Step3(id) ==
  LET r == round[id] IN
  /\ step[id] = S3
  /\ \E received \in SUBSET msgs2[r]:
    /\ Cardinality(received) >= N - T
    /\ LET Weights == [ v \in VALUES |->
             Cardinality({ m \in received: IsD2(m) /\ AsD2(m).v = v }) ]
       IN
       \/ \E v \in VALUES: 
          \* (a) If there are at least T+1 D-messages (2, r, v, D),
          \* then set x_P to v
          /\ Weights[v] >= T + 1
          /\ value' = [value EXCEPT ![id] = v]
          /\ IF 2 * Weights[v] > N + T
             THEN decision' = [decision EXCEPT ![id] = v]
             ELSE decision' = decision
       \/ /\ \A v \in VALUES: Weights[v] < T + 1
          /\ \E next_v \in VALUES:
             \* Choose a value with probability 1/2.
             \* We replace probabilites with non-determinism.
             /\ value' = [value EXCEPT ![id] = next_v]
    /\ step' = [ step EXCEPT ![id] = S3 ]
    /\ round' = [ round EXCEPT ![id] = r + 1 ]
    /\ UNCHANGED << msgs1, msgs2 >>

Next ==
  \E id \in CORRECT:
    \/ Step1(id)
    \/ Step2(id)
    \/ Step3(id)
    \* TODO: add a step by the faulty replicas?

======================================================================================