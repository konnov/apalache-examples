-------------------------- MODULE Ben_or83_inductive ------------------------------
(*
 * Inductive constructions for proving safety of AgreementInv for bounded parameters.
 *
 * Igor Konnov, August 2024
 *
 * - 2.5h to come up with Lemmas 1-9 for the fault-free case
 *
 * To make sure that we have constructed an inductive invariant, we need to check:
 *
 * 1. That IndInv => AgreementInv:
 *
 * 2. That Init => IndInv:
 *
 *
 * 3. That IndInit /\ Next => IndInv':
 *
 * $ seq 0 13 | parallel --delay 1 \
 *   ~/devl/apalache/bin/apalache-mc check --length=1 --inv=IndInv --init=IndInit \
 *   --tuning-options='search.invariantFilter=1-\>'state{} --out-dir={} MC_n6t1f0_inductive.tla
 *)
EXTENDS FiniteSets, Integers, typedefs, Ben_or83

TypeOK ==
  /\ value \in [ CORRECT -> VALUES ]
  /\ decision \in [ ALL -> VALUES \union { NO_DECISION } ]
  /\ round \in [ CORRECT -> ROUNDS ]
  /\ step \in [ CORRECT -> { S1, S2, S3 } ]
  /\ \E A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ]:
        msgs1 = [ r \in ROUNDS |-> { m \in A1: m.r = r } ]
  /\ \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
          A1Q \in SUBSET [ src: ALL, r: ROUNDS ]:
        msgs2 = [ r \in ROUNDS |->
            { D2(mm.src, r, mm.v): mm \in { m \in A1D: m.r = r } }
                \union { Q2(mm.src, r): mm \in { m \in A1Q: m.r = r } }
        ]

\*********** AUXILIARY DEFINITIONS ***********/
ExistsQuorum2(r, v) ==
  \* TODO: can we simplify this?
  \*\E S \in SUBSET msgs2[r]:
  LET S == msgs2[r] IN
  LET Sv == { m \in S: IsD2(m) /\ AsD2(m).v = v } IN
  /\ Cardinality(S) >= N - T
  /\ Cardinality(Sv) >= T + 1
  /\ 2 * Cardinality(Sv) > N + T

\*********** LEMMAS THAT CONSTITUTE THE INDUCTIVE INVARIANT ***********/

Lemma1_DecisionRequiresQuorum(id) ==
  decision[id] /= NO_DECISION =>
    \E r \in ROUNDS:
      /\ r <= round[id]
      /\ ExistsQuorum2(r, decision[id])

Lemma1_DecisionRequiresQuorumAll ==
  \A id \in CORRECT:
    Lemma1_DecisionRequiresQuorum(id)

Lemma2_NoEquivocation1ByCorrect ==
  \A r \in ROUNDS:
    \A m1, m2 \in msgs1[r]:
      m1.src = m2.src =>
        m1.src \in FAULTY \/ m1.v = m2.v

Lemma3_NoEquivocation2ByCorrect ==
  \A r \in ROUNDS:
    \A m1, m2 \in msgs2[r]:
      /\ IsD2(m1) /\ IsD2(m2) /\ AsD2(m1).src = AsD2(m2).src =>
        \/ AsD2(m1).src \in FAULTY
        \/ AsD2(m1).v = AsD2(m2).v
      /\ IsQ2(m1) /\ IsD2(m2) /\ AsQ2(m1).src = AsD2(m2).src =>
        AsQ2(m1).src \in FAULTY

Lemma4_MessagesNotFromFuture ==
  \A r \in ROUNDS:
    /\ \A m \in msgs1[r]:
      /\ step[m.src] /= S1 => (m.r <= round[m.src])
      /\ step[m.src] = S1 => (m.r < round[m.src])
    /\ \A m \in msgs2[r]:
      LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src IN
      LET mr == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r IN
      /\ step[src] = S3 => (mr <= round[src])
      /\ step[src] /= S3 => (mr < round[src])

Lemma5_RoundNeedsSentMessages ==
  \A id \in CORRECT:
    \A r \in ROUNDS:
      /\ r < round[id] \/ (r = round[id] /\ step[id] /= S1)
        => \E m \in msgs1[r]: m.src = id
      /\ r < round[id]
        => \E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id
      /\ (r = round[id] /\ step[id] = S3)
        => \E m \in msgs2[r]:
            \/ AsD2(m).src = id /\ AsD2(m).v = value[id]
            \/ AsQ2(m).src = id

Lemma6_DecisionDefinesValue ==
  \A id \in CORRECT:
    decision[id] /= NO_DECISION => value[id] = decision[id]

Lemma7_D2RequiresQuorum ==
  LET ExistsQuorum1(r, v) ==
    LET Sv == { m \in msgs1[r]: m.v = v } IN
    2 * Cardinality(Sv) > N + T
  IN
  \A r \in ROUNDS:
    \A v \in VALUES:
      (\E m \in msgs2[r]: IsD2(m) /\ AsD2(m).v = v)
        => ExistsQuorum1(r, v)

Lemma8_Q2RequiresNoQuorum ==
  LET RoundsWithQ2 ==
    { r \in ROUNDS:
      \E m \in msgs2[r]: IsQ2(m) /\ AsQ2(m).src \in CORRECT }
  IN
  \A r \in RoundsWithQ2:
    \* follows from Step2
    \E Q \in SUBSET ALL:
      /\ Cardinality(Q) >= N - T
      /\ Q \subseteq Senders1(msgs1[r])
      /\ \A v \in VALUES:
        LET Sv == Senders1({ m \in msgs1[r]: m.v = v /\ m.src \in Q }) IN
        2 * Cardinality(Sv) <= N

Lemma9_RoundsConnection ==
  \A r \in ROUNDS:
    r + 1 \in ROUNDS =>
      \* if there was a quorum of D2 messages for v in round r,
      \* then all messages by correct replicas carry v in round r + 1
      \A v \in VALUES:
        ExistsQuorum2(r, v) =>
          \A m \in msgs1[r + 1]:
            m.src \in CORRECT => m.v = v

\******** THE INDUCTIVE INVARIANT ***********/
IndInv ==
  /\ Lemma1_DecisionRequiresQuorumAll 
  /\ Lemma2_NoEquivocation1ByCorrect
  /\ Lemma3_NoEquivocation2ByCorrect
  /\ Lemma4_MessagesNotFromFuture
  /\ Lemma5_RoundNeedsSentMessages
  /\ Lemma6_DecisionDefinesValue
  /\ Lemma7_D2RequiresQuorum
  /\ Lemma8_Q2RequiresNoQuorum
  /\ Lemma9_RoundsConnection

\******** THE INDUCTIVE INVARIANT + THE SHAPE INVARIANT ***********/
IndInit ==
  /\ TypeOK
  /\ IndInv

======================================================================================