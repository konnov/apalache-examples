------------------- MODULE tendermint_single_indinv_proofs -------------------
(*
 * TLAPS proofs for the single-height Tendermint inductive invariant defined in
 * `tendermint_single_indinv.tla` (a machine-generated Apalache model).
 *
 * Goals (mirroring ben-or83/Ben_or83_proofs.tla):
 *   1. `TypedIndInvMin` is inductive: base case `Init => TypedIndInvMin`
 *      (Section B) and the step `TypedIndInvMin /\ Step => TypedIndInvMin'`
 *      (Section C).
 *   2. `TypedIndInvMin => Agreement` (Section D).
 *
 * We target `TypedIndInvMin` (IndTypeOk /\ IndInvMin, 17 conjuncts) first. If it
 * turns out not to be inductive, escalate to the full `TypedIndInv` (25
 * conjuncts). Targeting IndInvMin also keeps the two `ApaFoldSet` conjuncts
 * (which live only in the extra 8 conjuncts of IndInv and in IndInit) off the
 * proof's critical path; `Apalache.tla` is only a parse-time dependency here.
 *
 * Current status: the A/B/C/D skeleton is in place and the following are proved
 * end-to-end: the base case `InitInd` (Init => TypedIndInvMin), type preservation
 * `TypePres` (IndTypeOk'), and 4 inductive-step conjuncts --
 * `AllValidAndLockedRoundBounded`, `AllLockedRoundIffLockedValue`,
 * `AllValidRoundIffValidValue`, and `AllIfInDecidedThenValidDecision` --
 * plus the record-typing helpers used by TypePres. Still OMITTED (to be filled
 * in incrementally): the Section A quorum-intersection lemma, the remaining 12
 * inductive-step conjuncts, and the Section D agreement proof.
 *
 * Environment: tlapm (TLAPS) build `b064bce-dirty` (`tlapm --version`), using the
 * stdlib TLAPS + FiniteSetTheorems modules (no Isabelle backend; all obligations
 * discharged by Zenon/SMT). The spec `EXTENDS Apalache`; the community
 * `Apalache.tla` crashes this tlapm build (its `RECURSIVE ApaFoldSet` with a
 * higher-order operator argument trips the frontend), so a minimal parse-time
 * shim `Apalache.tla` sits in this directory (see its header). Verify with:
 *   tlapm --stretch 2 --threads 4 -I . tendermint_single_indinv_proofs.tla
 *   => "All 633 obligations proved"; every OMITTED stub contributes no
 *      obligation, exit 0.
 * Syntax/semantic checks while editing: SANY via tla2tools.jar.
 *
 * Igor Konnov, Claude Opus 4.8, July 2026
 *)
EXTENDS tendermint_single_indinv, FiniteSetTheorems, TLAPS

\* The actual number of faulty replicas. The spec declares no `F` constant, so we
\* define it here as the cardinality of the Faulty set.
F == Cardinality(Faulty)

\* TLAPS' standard proof of natural-number induction uses Isabelle. This workbench
\* runs without an Isabelle backend, so we trust the induction principle instead of
\* replaying that library proof. Needed for the round induction in Section D.
AXIOM NatInductionTrusted ==
  \A Q \in [Nat -> BOOLEAN] :
    (/\ Q[0]
     /\ \A n \in Nat : Q[n] => Q[n + 1])
      => \A n \in Nat : Q[n]

\*****************************************************************************
\* NAMED ASSUMPTIONS
\*
\* The Apalache spec declares no module-level ASSUME. We state the parameter
\* constraints the proofs rely on under names, so steps can USE/cite them.
\* Resilience (confirmed with the spec author): N > 3*T /\ T >= F /\ F >= 0.
\*****************************************************************************

\* Tendermint/BFT resilience: strictly more than three times the fault bound.
ASSUME NgtT == N > 3 * T

\* The optimal BFT replica count (confirmed by the spec author). REQUIRED for quorum
\* intersection: with a fixed 2T+1 quorum threshold, two quorums share a *correct*
\* process only when N = 3T+1. Without it QuorumsIntersectInCorrect is FALSE, e.g.
\* N=5, T=1, F=1, A={c1,c2,f}, B={c3,c4,f}: both have size 2T+1=3 but meet only in
\* the faulty node; agreement fails for N>3T+1 (a 2T+1 quorum is below 2/3 of N).
ASSUME Neq3Tp1 == N = 3 * T + 1

\* The actual number of faults is bounded by T.
ASSUME TgeF == T >= F

\* The number of faults is non-negative.
ASSUME FnonNeg == F >= 0

\* Correct and faulty replicas are disjoint.
ASSUME DisjointCF == Corr \cap Faulty = {}

\* Cardinality is only meaningful for finite sets; there are finitely many replicas.
ASSUME FiniteCF == IsFiniteSet(Corr) /\ IsFiniteSet(Faulty)

\* N counts all replicas (correct + faulty), which are disjoint.
ASSUME NCard == N = Cardinality(Corr) + Cardinality(Faulty)

\* The protocol parameters are natural numbers.
ASSUME ConstNat == N \in Nat /\ T \in Nat /\ MaxRound \in Nat

\* Nil is encoded as -1 and is not a valid value. (Confirmed by the spec's use of
\* -1 as the nil sentinel throughout; TODO: confirm with the spec author.)
ASSUME NilNotValid == -1 \notin ValidValues

\* There is at least one valid value to propose. Needed by the base case for the
\* existential witness inside AllNoEquivocationByCorrect over empty message logs.
ASSUME ValidValuesNonEmpty == ValidValues # {}

LEMMA IntLeGeTrans ==
  ASSUME NEW a \in Int, NEW b \in Int, NEW c \in Int, NEW k \in Int,
         a >= k, a <= b, b <= c
  PROVE  c >= k
  BY SMT

LEMMA IntLeGeTrans1 ==
  ASSUME NEW a \in Int, NEW b \in Int, NEW k \in Int,
         a >= k, a <= b
  PROVE  b >= k
  BY SMT

\*****************************************************************************
\* SECTION A -- FOUNDATIONAL CARDINALITY / QUORUM LEMMAS
\*
\* Port from ben-or83/Ben_or83_proofs.tla Section A, adapted to Tendermint's
\* 2T+1 quorums under N > 3*T. The central fact is that any two >= 2T+1 subsets
\* of (Corr \union Faulty) share a *correct* process (since 2*(2T+1) - N > T >= F).
\* The worked example in Section C does not need these; they are stubbed here.
\*****************************************************************************

\* Two quorums of size >= 2T+1 intersect in a correct process. TODO: prove by
\* porting the Ben-Or QuorumIntersection argument (inclusion-exclusion on
\* Cardinality over the finite set Corr \union Faulty).
THEOREM QuorumsIntersectInCorrect ==
  ASSUME NEW A \in SUBSET (Corr \union Faulty),
         NEW B \in SUBSET (Corr \union Faulty),
         Cardinality(A) >= 2 * T + 1,
         Cardinality(B) >= 2 * T + 1
  PROVE  \E c \in Corr : c \in A /\ c \in B
  <1> DEFINE U == Corr \union Faulty
  <1> DEFINE I == A \cap B
  <1> DEFINE IC == I \cap Corr
  <1> DEFINE IFa == I \cap Faulty
  <1>finU. IsFiniteSet(U)  BY FiniteCF, FS_Union
  <1>AsubU. A \subseteq U  OBVIOUS
  <1>BsubU. B \subseteq U  OBVIOUS
  <1>finA. IsFiniteSet(A)  BY <1>finU, <1>AsubU, FS_Subset
  <1>finB. IsFiniteSet(B)  BY <1>finU, <1>BsubU, FS_Subset
  <1>IsubU. I \subseteq U  OBVIOUS
  <1>finI. IsFiniteSet(I)  BY <1>finU, <1>IsubU, FS_Subset
  <1>ICsubU. IC \subseteq U  OBVIOUS
  <1>finIC. IsFiniteSet(IC)  BY <1>finU, <1>ICsubU, FS_Subset
  <1>IFasubFa. IFa \subseteq Faulty  OBVIOUS
  <1>finIFa. IsFiniteSet(IFa)  BY FiniteCF, <1>IFasubFa, FS_Subset
  <1>unionSubU. (A \cup B) \subseteq U  OBVIOUS
  <1>finX. /\ IsFiniteSet(Corr \cap Faulty) /\ IsFiniteSet(IC \cup IFa)
           /\ IsFiniteSet(IC \cap IFa) /\ IsFiniteSet(A \cup B)
      <2>1. (Corr \cap Faulty) \subseteq Corr  OBVIOUS
      <2>2. (IC \cup IFa) \subseteq U /\ (IC \cap IFa) \subseteq U /\ (A \cup B) \subseteq U  OBVIOUS
      <2> QED  BY <2>1, <2>2, <1>finU, FiniteCF, FS_Subset
  <1>types. /\ Cardinality(A) \in Nat /\ Cardinality(B) \in Nat /\ Cardinality(I) \in Nat
            /\ Cardinality(IC) \in Nat /\ Cardinality(IFa) \in Nat /\ Cardinality(A \cup B) \in Nat
            /\ Cardinality(Faulty) \in Nat /\ Cardinality(Corr) \in Nat /\ Cardinality(U) \in Nat
            /\ Cardinality(Corr \cap Faulty) \in Nat /\ Cardinality(IC \cup IFa) \in Nat
            /\ Cardinality(IC \cap IFa) \in Nat
      BY <1>finA, <1>finB, <1>finI, <1>finIC, <1>finIFa, <1>finU, <1>finX, FiniteCF, FS_CardinalityType
  <1>cardU. Cardinality(U) = N
      <2>1. Cardinality(U) = Cardinality(Corr) + Cardinality(Faulty) - Cardinality(Corr \cap Faulty)
            BY FiniteCF, FS_Union
      <2>2. Cardinality(Corr \cap Faulty) = 0
            BY DisjointCF, FS_EmptySet
      <2> QED  BY <2>1, <2>2, NCard, <1>types, SMT
  <1>cardUnion. Cardinality(A \cup B) = Cardinality(A) + Cardinality(B) - Cardinality(I)
      BY <1>finA, <1>finB, FS_Union
  <1>cardUnionLeN. Cardinality(A \cup B) <= N
      BY <1>finU, <1>unionSubU, FS_Subset, <1>cardU
  <1>cardI. Cardinality(I) >= 4 * T + 2 - N
      BY <1>cardUnion, <1>cardUnionLeN, <1>types, ConstNat, SMT
  <1>Ipart. I = IC \cup IFa  BY <1>IsubU
  <1>disj. IC \cap IFa = {}  BY DisjointCF
  <1>cardIeq. Cardinality(I) = Cardinality(IC) + Cardinality(IFa)
      <2>1. Cardinality(IC \cup IFa) = Cardinality(IC) + Cardinality(IFa) - Cardinality(IC \cap IFa)
            BY <1>finIC, <1>finIFa, FS_Union
      <2>2. Cardinality(IC \cap IFa) = 0  BY <1>disj, FS_EmptySet
      <2> QED  BY <2>1, <2>2, <1>Ipart, <1>types, SMT
  <1>cardIFaLeF. Cardinality(IFa) <= Cardinality(Faulty)
      BY <1>IFasubFa, FiniteCF, FS_Subset
  <1>cardICge. Cardinality(IC) >= 4 * T + 2 - N - Cardinality(Faulty)
      BY <1>cardI, <1>cardIeq, <1>cardIFaLeF, <1>types, ConstNat, SMT
  <1>pos. Cardinality(IC) >= 1
      \* 4T+2-N-F = 4T+2-(3T+1)-F = T+1-F >= 1, using N = 3T+1 and Cardinality(Faulty) = F <= T
      BY <1>cardICge, <1>types, Neq3Tp1, TgeF, ConstNat DEF F
  <1>ne. IC # {}
      BY <1>pos, <1>finIC, FS_EmptySet
  <1> QED
      <2> PICK c \in IC : TRUE  BY <1>ne
      <2> QED  OBVIOUS

\* A single quorum (>= 2T+1 senders) already contains a correct process.
THEOREM QuorumHasCorrect ==
  ASSUME NEW S \in SUBSET (Corr \union Faulty), Cardinality(S) >= 2 * T + 1
  PROVE  \E c \in Corr : c \in S
  BY QuorumsIntersectInCorrect

\*****************************************************************************
\* SECTION B -- BASE CASE + TYPE PRESERVATION
\*****************************************************************************

\* Base case of induction. At Init the message logs are empty and every
\* per-process field is nil (-1) or 0, so each IndInvMin conjunct holds: the
\* message-quantified ones are vacuous, the nil-flag ones agree, and the two
\* existential-witness conjuncts (AllNoEquivocationByCorrect, PrecommitsLockValue)
\* close via ValidValuesNonEmpty and Cardinality({}) = 0.
THEOREM InitInd ==
  Init => TypedIndInvMin
  <1> SUFFICES ASSUME Init PROVE TypedIndInvMin
      OBVIOUS
  <1> USE ConstNat DEF Init
  \* the empty logs / nil flags, exposed for every conjunct below
  <1>e. /\ \A r \in (0)..(MaxRound) :
              msgs_propose[r] = {} /\ msgs_prevote[r] = {} /\ msgs_precommit[r] = {}
        /\ \A p \in Corr :
              round[p] = 0 /\ step[p] = "PROPOSE_OF_STEP" /\ decision[p] = -1
              /\ locked_value[p] = -1 /\ locked_round[p] = -1
              /\ valid_value[p] = -1 /\ valid_round[p] = -1
        OBVIOUS
  <1>type. IndTypeOk
        BY SMT DEF IndTypeOk
  <1>1.  AllNoFutureMessagesSent
        BY <1>e, SMT DEF AllNoFutureMessagesSent
  <1>2.  AllIfInPrevoteThenSentPrevote
        BY <1>e DEF AllIfInPrevoteThenSentPrevote
  <1>3.  AllIfInPrecommitThenSentPrecommit
        BY <1>e DEF AllIfInPrecommitThenSentPrecommit
  <1>4.  AllIfInDecidedThenReceivedProposal
        BY <1>e DEF AllIfInDecidedThenReceivedProposal
  <1>5.  AllIfInDecidedThenReceivedTwoThirds
        BY <1>e DEF AllIfInDecidedThenReceivedTwoThirds
  <1>6.  AllIfInDecidedThenValidDecision
        BY <1>e, NilNotValid, SMT DEF AllIfInDecidedThenValidDecision
  <1>7.  AllLockedRoundIffLockedValue
        BY <1>e DEF AllLockedRoundIffLockedValue
  <1>8.  AllValidRoundIffValidValue
        BY <1>e DEF AllValidRoundIffValidValue
  <1>9.  AllValidAndLockedRoundBounded
        BY <1>e, SMT DEF AllValidAndLockedRoundBounded
  <1>10. AllIfValidRoundThenTwoThirdsPrevotes
        BY <1>e DEF AllIfValidRoundThenTwoThirdsPrevotes
  <1>11. AllIfLockedRoundThenSentCommit
        BY <1>e DEF AllIfLockedRoundThenSentCommit
  <1>12. AllLatestPrecommitHasLockedRound
        BY <1>e DEF AllLatestPrecommitHasLockedRound
  <1>13. AllIfSentPrevoteThenReceivedProposalOrTwoThirds
        BY <1>e DEF AllIfSentPrevoteThenReceivedProposalOrTwoThirds
  <1>14. IfSentPrecommitThenSentPrevote
        BY <1>e DEF IfSentPrecommitThenSentPrevote
  <1>15. IfSentPrecommitThenReceivedTwoThirds
        BY <1>e DEF IfSentPrecommitThenReceivedTwoThirds
  <1>16. AllNoEquivocationByCorrect
        BY <1>e, ValidValuesNonEmpty DEF AllNoEquivocationByCorrect
  <1>17. PrecommitsLockValue
    <2> SUFFICES ASSUME NEW r \in (0)..(MaxRound), NEW v \in ValidValues
                 PROVE  Cardinality({s \in (Corr \union Faulty) :
                           \E m \in {mm \in msgs_precommit[r] : v = mm.id} : s = m.src}) < 2 * T + 1
        BY DEF PrecommitsLockValue
    <2>1. msgs_precommit[r] = {}
          BY <1>e
    <2>2. {mm \in msgs_precommit[r] : v = mm.id} = {}
          BY <2>1, FS_EmptySet
    <2>3. {s \in (Corr \union Faulty) :
             \E m \in {mm \in msgs_precommit[r] : v = mm.id} : s = m.src} = {}
          BY <2>2, FS_EmptySet
    <2>4. Cardinality({s \in (Corr \union Faulty) :
             \E m \in {mm \in msgs_precommit[r] : v = mm.id} : s = m.src}) = 0
          BY <2>3, FS_EmptySet
    <2>5. 0 < 2 * T + 1
          BY ConstNat, SMT
    <2> QED BY <2>4, <2>5
  <1> QED
      BY <1>type, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
         <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17
      DEF TypedIndInvMin, IndInvMin

\* Record-typing helpers: a freshly built message record lies in the IndTypeOk
\* element set. These supply the tuple witness that Zenon/SMT cannot guess for
\* `rec \in {[..]: t \in A \X B \X ...}` goals. Used by TypePres for the
\* message-adding actions (both correct broadcasts and FaultyStep injections).
LEMMA ProposeRecTyped ==
  ASSUME NEW s \in (Corr \union Faulty), NEW rr \in (0)..(MaxRound),
         NEW pr \in ((ValidValues \union InvalidValues) \union {-1}),
         NEW vr \in ((0)..(MaxRound) \union {-1})
  PROVE  [proposal |-> pr, round |-> rr, src |-> s, valid_round |-> vr]
           \in {[proposal |-> t[3], round |-> t[2], src |-> t[1], valid_round |-> t[4]]:
                  t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1})) \X (((0)..(MaxRound) \union {-1}))}
  <1>1. <<s, rr, pr, vr>> \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1})) \X (((0)..(MaxRound) \union {-1}))
        OBVIOUS
  <1> QED BY <1>1, SMT

LEMMA PrevoteRecTyped ==
  ASSUME NEW s \in (Corr \union Faulty), NEW rr \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  [id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rr, src |-> s]
           \in {[id |-> t[3], kind |-> "PREVOTE_OF_VOTEKIND", round |-> t[2], src |-> t[1]]:
                  t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
  <1>1. <<s, rr, idv>> \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))
        OBVIOUS
  <1> QED BY <1>1, SMT

LEMMA PrecommitRecTyped ==
  ASSUME NEW s \in (Corr \union Faulty), NEW rr \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  [id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> rr, src |-> s]
           \in {[id |-> t[3], kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> t[2], src |-> t[1]]:
                  t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
  <1>1. <<s, rr, idv>> \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))
        OBVIOUS
  <1> QED BY <1>1, SMT

\* Message monotonicity: every Step action either leaves a message log unchanged
\* or appends to it (EXCEPT-union), so entries are never removed. Used by the
\* Section C "in step X => already sent Y" conjuncts to carry a witnessing
\* message across a step.
LEMMA ProposeMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound), NEW x \in msgs_propose[r]
  PROVE  x \in msgs_propose'[r]
  <1> USE DEF IndTypeOk
  <1>sel. msgs_propose' = msgs_propose \/ (\E p \in Corr : InsertProposal(p)) \/ FaultyStep
      BY DEF Step
  <1>1. CASE msgs_propose' = msgs_propose  BY <1>1
  <1>2. CASE \E p \in Corr : InsertProposal(p)
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_propose' = [msgs_propose EXCEPT ![idx] = (msgs_propose[idx] \union S)]
            BY <1>2 DEF InsertProposal
      <2> QED  BY <2>1, SMT
  <1>3. CASE FaultyStep
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_propose' = [msgs_propose EXCEPT ![idx] = (msgs_propose[idx] \union S)]
            BY <1>3 DEF FaultyStep
      <2> QED  BY <2>1, SMT
  <1> QED  BY <1>sel, <1>1, <1>2, <1>3

LEMMA PrevoteMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound), NEW x \in msgs_prevote[r]
  PROVE  x \in msgs_prevote'[r]
  <1> USE DEF IndTypeOk
  <1>sel. \/ msgs_prevote' = msgs_prevote
          \/ \E p \in Corr : UponProposalInPropose(p)
          \/ \E p \in Corr : UponProposalInProposeAndPrevote(p)
          \/ \E p \in Corr : OnTimeoutPropose(p)
          \/ FaultyStep
      BY DEF Step
  <1>1. CASE msgs_prevote' = msgs_prevote  BY <1>1
  <1>2. CASE \E p \in Corr : UponProposalInPropose(p)
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_prevote' = [msgs_prevote EXCEPT ![idx] = (msgs_prevote[idx] \union S)]
            BY <1>2 DEF UponProposalInPropose
      <2> QED  BY <2>1, SMT
  <1>3. CASE \E p \in Corr : UponProposalInProposeAndPrevote(p)
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_prevote' = [msgs_prevote EXCEPT ![idx] = (msgs_prevote[idx] \union S)]
            BY <1>3 DEF UponProposalInProposeAndPrevote
      <2> QED  BY <2>1, SMT
  <1>4. CASE \E p \in Corr : OnTimeoutPropose(p)
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_prevote' = [msgs_prevote EXCEPT ![idx] = (msgs_prevote[idx] \union S)]
            BY <1>4 DEF OnTimeoutPropose
      <2> QED  BY <2>1, SMT
  <1>5. CASE FaultyStep
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_prevote' = [msgs_prevote EXCEPT ![idx] = (msgs_prevote[idx] \union S)]
            BY <1>5 DEF FaultyStep
      <2> QED  BY <2>1, SMT
  <1> QED  BY <1>sel, <1>1, <1>2, <1>3, <1>4, <1>5

LEMMA PrecommitMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound), NEW x \in msgs_precommit[r]
  PROVE  x \in msgs_precommit'[r]
  <1> USE DEF IndTypeOk
  <1>sel. \/ msgs_precommit' = msgs_precommit
          \/ \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
          \/ \E p \in Corr : UponQuorumOfPrevotesAny(p)
          \/ \E p \in Corr : OnQuorumOfNilPrevotes(p)
          \/ FaultyStep
      BY DEF Step
  <1>1. CASE msgs_precommit' = msgs_precommit  BY <1>1
  <1>2. CASE \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
      \* then-branch appends, else leaves unchanged; either way x persists
      <2>1. msgs_precommit' = msgs_precommit
            \/ (\E idx \in (0)..(MaxRound) : \E S : msgs_precommit' = [msgs_precommit EXCEPT ![idx] = (msgs_precommit[idx] \union S)])
            BY <1>2 DEF UponProposalInPrevoteOrCommitAndPrevote
      <2> QED  BY <2>1, SMT
  <1>3. CASE \E p \in Corr : UponQuorumOfPrevotesAny(p)
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_precommit' = [msgs_precommit EXCEPT ![idx] = (msgs_precommit[idx] \union S)]
            BY <1>3 DEF UponQuorumOfPrevotesAny
      <2> QED  BY <2>1, SMT
  <1>4. CASE \E p \in Corr : OnQuorumOfNilPrevotes(p)
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_precommit' = [msgs_precommit EXCEPT ![idx] = (msgs_precommit[idx] \union S)]
            BY <1>4 DEF OnQuorumOfNilPrevotes
      <2> QED  BY <2>1, SMT
  <1>5. CASE FaultyStep
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_precommit' = [msgs_precommit EXCEPT ![idx] = (msgs_precommit[idx] \union S)]
            BY <1>5 DEF FaultyStep
      <2> QED  BY <2>1, SMT
  <1> QED  BY <1>sel, <1>1, <1>2, <1>3, <1>4, <1>5

LEMMA PrevoteSenderSetCardinalityMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote'[r] : mm.id = idv} : s = m.src})
  <1> DEFINE Old == {s \in (Corr \union Faulty) :
                       \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src}
              New == {s \in (Corr \union Faulty) :
                       \E m \in {mm \in msgs_prevote'[r] : mm.id = idv} : s = m.src}
  <1>sub. Old \subseteq New
        BY PrevoteMonotone DEF Old, New
  <1>newSub. New \subseteq (Corr \union Faulty)
        BY DEF New
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finNew. IsFiniteSet(New)
        BY <1>newSub, <1>finCF, FS_Subset
  <1> QED
        BY <1>sub, <1>finNew, FS_Subset

LEMMA PrevoteAllSenderSetCardinalityMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound)
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote'[r] : s = m.src})
  <1> DEFINE Old == {s \in (Corr \union Faulty) :
                       \E m \in msgs_prevote[r] : s = m.src}
              New == {s \in (Corr \union Faulty) :
                       \E m \in msgs_prevote'[r] : s = m.src}
  <1>sub. Old \subseteq New
        BY PrevoteMonotone DEF Old, New
  <1>newSub. New \subseteq (Corr \union Faulty)
        BY DEF New
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finNew. IsFiniteSet(New)
        BY <1>newSub, <1>finCF, FS_Subset
  <1> QED
        BY <1>sub, <1>finNew, FS_Subset

LEMMA PrevoteValueSenderSetCardinalityLeAllSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
  <1> DEFINE ValueSenders == {s \in (Corr \union Faulty) :
                                \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src}
              AllSenders == {s \in (Corr \union Faulty) :
                                \E m \in msgs_prevote[r] : s = m.src}
  <1>sub. ValueSenders \subseteq AllSenders
        BY DEF ValueSenders, AllSenders
  <1>allSub. AllSenders \subseteq (Corr \union Faulty)
        BY DEF AllSenders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finAll. IsFiniteSet(AllSenders)
        BY <1>allSub, <1>finCF, FS_Subset
  <1> QED
        BY <1>sub, <1>finAll, FS_Subset

LEMMA PrevoteEvidenceSenderSetCardinalityLeAllSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound), NEW E \in SUBSET msgs_prevote[r]
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in E : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
  <1> DEFINE EvidenceSenders == {s \in (Corr \union Faulty) :
                                   \E m \in E : s = m.src}
              AllSenders == {s \in (Corr \union Faulty) :
                                \E m \in msgs_prevote[r] : s = m.src}
  <1>sub. EvidenceSenders \subseteq AllSenders
        BY DEF EvidenceSenders, AllSenders
  <1>allSub. AllSenders \subseteq (Corr \union Faulty)
        BY DEF AllSenders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finAll. IsFiniteSet(AllSenders)
        BY <1>allSub, <1>finCF, FS_Subset
  <1> QED
        BY <1>sub, <1>finAll, FS_Subset

LEMMA PrecommitSenderSetCardinalityMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_precommit[r] : mm.id = idv} : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_precommit'[r] : mm.id = idv} : s = m.src})
  <1> DEFINE Old == {s \in (Corr \union Faulty) :
                       \E m \in {mm \in msgs_precommit[r] : mm.id = idv} : s = m.src}
              New == {s \in (Corr \union Faulty) :
                       \E m \in {mm \in msgs_precommit'[r] : mm.id = idv} : s = m.src}
  <1>sub. Old \subseteq New
        BY PrecommitMonotone DEF Old, New
  <1>newSub. New \subseteq (Corr \union Faulty)
        BY DEF New
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finNew. IsFiniteSet(New)
        BY <1>newSub, <1>finCF, FS_Subset
  <1> QED
        BY <1>sub, <1>finNew, FS_Subset

LEMMA PrecommitValueMessagesCardinalityLeSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({m \in msgs_precommit[r] : m.id = idv})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_precommit[r] : mm.id = idv} : s = m.src})
  <1> DEFINE Msgs == {m \in msgs_precommit[r] : m.id = idv}
              Senders == {s \in (Corr \union Faulty) : \E m \in Msgs : s = m.src}
              SrcOf == [m \in Msgs |-> m.src]
  <1>sendersSub. Senders \subseteq (Corr \union Faulty)
        BY DEF Senders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finSenders. IsFiniteSet(Senders)
        BY <1>sendersSub, <1>finCF, FS_Subset
  <1>dom. DOMAIN SrcOf = Msgs
        BY DEF SrcOf
  <1>range. \A x \in Msgs : SrcOf[x] \in Senders
        BY SMT DEF SrcOf, Senders, Msgs, IndTypeOk
  <1>fun. SrcOf \in [Msgs -> Senders]
        BY <1>dom, <1>range, SMT
  <1>one. \A x \in Msgs : \A y \in Msgs : SrcOf[x] = SrcOf[y] => x = y
        BY SMT DEF SrcOf, Msgs, IndTypeOk
  <1>inj. SrcOf \in Injection(Msgs, Senders)
        BY <1>fun, <1>one DEF Injection, IsInjective
  <1> QED
        BY <1>inj, <1>finSenders, FS_Injection

LEMMA PrecommitValueMessagesFinite ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  IsFiniteSet({m \in msgs_precommit[r] : m.id = idv})
  <1> DEFINE Msgs == {m \in msgs_precommit[r] : m.id = idv}
              Senders == {s \in (Corr \union Faulty) : \E m \in Msgs : s = m.src}
              SrcOf == [m \in Msgs |-> m.src]
  <1>sendersSub. Senders \subseteq (Corr \union Faulty)
        BY DEF Senders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finSenders. IsFiniteSet(Senders)
        BY <1>sendersSub, <1>finCF, FS_Subset
  <1>dom. DOMAIN SrcOf = Msgs
        BY DEF SrcOf
  <1>range. \A x \in Msgs : SrcOf[x] \in Senders
        BY SMT DEF SrcOf, Senders, Msgs, IndTypeOk
  <1>fun. SrcOf \in [Msgs -> Senders]
        BY <1>dom, <1>range, SMT
  <1>one. \A x \in Msgs : \A y \in Msgs : SrcOf[x] = SrcOf[y] => x = y
        BY SMT DEF SrcOf, Msgs, IndTypeOk
  <1>inj. SrcOf \in Injection(Msgs, Senders)
        BY <1>fun, <1>one DEF Injection, IsInjective
  <1> QED
        BY <1>inj, <1>finSenders, FS_Injection

LEMMA PrevoteValueMessagesCardinalityLeSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({m \in msgs_prevote[r] : m.id = idv})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src})
  <1> DEFINE Msgs == {m \in msgs_prevote[r] : m.id = idv}
              Senders == {s \in (Corr \union Faulty) : \E m \in Msgs : s = m.src}
              SrcOf == [m \in Msgs |-> m.src]
  <1>sendersSub. Senders \subseteq (Corr \union Faulty)
        BY DEF Senders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finSenders. IsFiniteSet(Senders)
        BY <1>sendersSub, <1>finCF, FS_Subset
  <1>dom. DOMAIN SrcOf = Msgs
        BY DEF SrcOf
  <1>range. \A x \in Msgs : SrcOf[x] \in Senders
        BY SMT DEF SrcOf, Senders, Msgs, IndTypeOk
  <1>fun. SrcOf \in [Msgs -> Senders]
        BY <1>dom, <1>range, SMT
  <1>one. \A x \in Msgs : \A y \in Msgs : SrcOf[x] = SrcOf[y] => x = y
        BY SMT DEF SrcOf, Msgs, IndTypeOk
  <1>inj. SrcOf \in Injection(Msgs, Senders)
        BY <1>fun, <1>one DEF Injection, IsInjective
  <1> QED
        BY <1>inj, <1>finSenders, FS_Injection

LEMMA PrevoteValueMessagesCardinalityLeAllSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({m \in msgs_prevote[r] : m.id = idv})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
  <1> DEFINE Msgs == {m \in msgs_prevote[r] : m.id = idv}
              Senders == {s \in (Corr \union Faulty) : \E m \in msgs_prevote[r] : s = m.src}
              SrcOf == [m \in Msgs |-> m.src]
  <1>sendersSub. Senders \subseteq (Corr \union Faulty)
        BY DEF Senders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finSenders. IsFiniteSet(Senders)
        BY <1>sendersSub, <1>finCF, FS_Subset
  <1>dom. DOMAIN SrcOf = Msgs
        BY DEF SrcOf
  <1>range. \A x \in Msgs : SrcOf[x] \in Senders
        BY SMT DEF SrcOf, Senders, Msgs, IndTypeOk
  <1>fun. SrcOf \in [Msgs -> Senders]
        BY <1>dom, <1>range, SMT
  <1>one. \A x \in Msgs : \A y \in Msgs : SrcOf[x] = SrcOf[y] => x = y
        BY SMT DEF SrcOf, Msgs, IndTypeOk
  <1>inj. SrcOf \in Injection(Msgs, Senders)
        BY <1>fun, <1>one DEF Injection, IsInjective
  <1> QED
        BY <1>inj, <1>finSenders, FS_Injection

LEMMA PrevoteValueMessagesFinite ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  IsFiniteSet({m \in msgs_prevote[r] : m.id = idv})
  <1> DEFINE Msgs == {m \in msgs_prevote[r] : m.id = idv}
              Senders == {s \in (Corr \union Faulty) : \E m \in Msgs : s = m.src}
              SrcOf == [m \in Msgs |-> m.src]
  <1>sendersSub. Senders \subseteq (Corr \union Faulty)
        BY DEF Senders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finSenders. IsFiniteSet(Senders)
        BY <1>sendersSub, <1>finCF, FS_Subset
  <1>dom. DOMAIN SrcOf = Msgs
        BY DEF SrcOf
  <1>range. \A x \in Msgs : SrcOf[x] \in Senders
        BY SMT DEF SrcOf, Senders, Msgs, IndTypeOk
  <1>fun. SrcOf \in [Msgs -> Senders]
        BY <1>dom, <1>range, SMT
  <1>one. \A x \in Msgs : \A y \in Msgs : SrcOf[x] = SrcOf[y] => x = y
        BY SMT DEF SrcOf, Msgs, IndTypeOk
  <1>inj. SrcOf \in Injection(Msgs, Senders)
        BY <1>fun, <1>one DEF Injection, IsInjective
  <1> QED
        BY <1>inj, <1>finSenders, FS_Injection

LEMMA StepUpdateChangedProcess ==
  ASSUME IndTypeOk, NEW p \in Corr, NEW q \in Corr, NEW st,
         step' = [step EXCEPT ![p] = st],
         step'[q] # step[q]
  PROVE  q = p
  BY SMT DEF IndTypeOk

\* If a correct process q's step changed over Step, then q is the acting process
\* and took one of its nine step-changing actions. (InsertProposal and FaultyStep
\* leave step unchanged; every other action sets step via [step EXCEPT ![p] = ..],
\* so a change at q forces q = p.) Used to identify the enabling action from the
\* post-state in the Section C "in step X" conjuncts.
LEMMA StepChangeChar ==
  ASSUME IndTypeOk, Step, NEW q \in Corr, step'[q] # step[q]
  PROVE  \/ UponProposalInPropose(q) \/ UponProposalInProposeAndPrevote(q)
         \/ UponQuorumOfPrevotesAny(q) \/ UponProposalInPrevoteOrCommitAndPrevote(q)
         \/ UponQuorumOfPrecommitsAny(q) \/ UponProposalInPrecommitNoDecision(q)
         \/ OnTimeoutPropose(q) \/ OnQuorumOfNilPrevotes(q) \/ OnRoundCatchup(q)
  <1> USE DEF IndTypeOk
  <1>sel. \/ step' = step
          \/ \E p \in Corr : UponProposalInPropose(p)
          \/ \E p \in Corr : UponProposalInProposeAndPrevote(p)
          \/ \E p \in Corr : UponQuorumOfPrevotesAny(p)
          \/ \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
          \/ \E p \in Corr : UponQuorumOfPrecommitsAny(p)
          \/ \E p \in Corr : UponProposalInPrecommitNoDecision(p)
          \/ \E p \in Corr : OnTimeoutPropose(p)
          \/ \E p \in Corr : OnQuorumOfNilPrevotes(p)
          \/ \E p \in Corr : OnRoundCatchup(p)
      BY DEF Step
  <1>0. CASE step' = step
      BY <1>0
  <1>1. CASE \E p \in Corr : UponProposalInPropose(p)
    <2> PICK p \in Corr : UponProposalInPropose(p) BY <1>1
    <2>1. step' = [step EXCEPT ![p] = "PREVOTE_OF_STEP"] BY DEF UponProposalInPropose
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>1, <2>2
  <1>2. CASE \E p \in Corr : UponProposalInProposeAndPrevote(p)
    <2> PICK p \in Corr : UponProposalInProposeAndPrevote(p) BY <1>2
    <2>1. step' = [step EXCEPT ![p] = "PREVOTE_OF_STEP"] BY DEF UponProposalInProposeAndPrevote
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>2, <2>2
  <1>3. CASE \E p \in Corr : UponQuorumOfPrevotesAny(p)
    <2> PICK p \in Corr : UponQuorumOfPrevotesAny(p) BY <1>3
    <2>1. step' = [step EXCEPT ![p] = "PRECOMMIT_OF_STEP"] BY DEF UponQuorumOfPrevotesAny
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>3, <2>2
  <1>4. CASE \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
    <2> PICK p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p) BY <1>4
    <2>1. step' = step \/ step' = [step EXCEPT ![p] = "PRECOMMIT_OF_STEP"]
          BY DEF UponProposalInPrevoteOrCommitAndPrevote
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>4, <2>2
  <1>5. CASE \E p \in Corr : UponQuorumOfPrecommitsAny(p)
    <2> PICK p \in Corr : UponQuorumOfPrecommitsAny(p) BY <1>5
    <2>1. step' = [step EXCEPT ![p] = "PROPOSE_OF_STEP"] BY DEF UponQuorumOfPrecommitsAny
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>5, <2>2
  <1>6. CASE \E p \in Corr : UponProposalInPrecommitNoDecision(p)
    <2> PICK p \in Corr : UponProposalInPrecommitNoDecision(p) BY <1>6
    <2>1. step' = [step EXCEPT ![p] = "DECIDED_OF_STEP"] BY DEF UponProposalInPrecommitNoDecision
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>6, <2>2
  <1>7. CASE \E p \in Corr : OnTimeoutPropose(p)
    <2> PICK p \in Corr : OnTimeoutPropose(p) BY <1>7
    <2>1. step' = [step EXCEPT ![p] = "PREVOTE_OF_STEP"] BY DEF OnTimeoutPropose
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>7, <2>2
  <1>8. CASE \E p \in Corr : OnQuorumOfNilPrevotes(p)
    <2> PICK p \in Corr : OnQuorumOfNilPrevotes(p) BY <1>8
    <2>1. step' = [step EXCEPT ![p] = "PRECOMMIT_OF_STEP"] BY DEF OnQuorumOfNilPrevotes
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>8, <2>2
  <1>9. CASE \E p \in Corr : OnRoundCatchup(p)
    <2> PICK p \in Corr : OnRoundCatchup(p) BY <1>9
    <2>1. step' = [step EXCEPT ![p] = "PROPOSE_OF_STEP"] BY DEF OnRoundCatchup
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>9, <2>2
  <1> QED BY <1>sel, <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9

LEMMA EnteredPrevoteHasSentPrevote ==
  ASSUME TypedIndInvMin, Step, NEW q \in Corr,
         step[q] # "PREVOTE_OF_STEP", step'[q] = "PREVOTE_OF_STEP"
  PROVE  \E m \in msgs_prevote'[round'[q]] :
           /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
           /\ q = m.src
  BY SMT DEF TypedIndInvMin, IndInvMin, IndTypeOk, Step, InsertProposal,
     UponProposalInPropose, UponProposalInProposeAndPrevote,
     UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
     UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
     OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup, FaultyStep

LEMMA EnteredPrecommitHasSentPrecommit ==
  ASSUME TypedIndInvMin, Step, NEW q \in Corr,
         step[q] # "PRECOMMIT_OF_STEP", step'[q] = "PRECOMMIT_OF_STEP"
  PROVE  \E m \in msgs_precommit'[round'[q]] :
           /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
           /\ q = m.src
  BY SMT DEF TypedIndInvMin, IndInvMin, IndTypeOk, Step, InsertProposal,
     UponProposalInPropose, UponProposalInProposeAndPrevote,
     UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
     UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
     OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup, FaultyStep

LEMMA RoundMonotone ==
  ASSUME IndTypeOk, Step, NEW q \in Corr
  PROVE  round[q] <= round'[q]
  BY SMT DEF IndTypeOk, Step, UponQuorumOfPrecommitsAny, OnRoundCatchup

\* Type preservation, grouped by type conjunct: each state variable is touched
\* by only a few Step actions; for all other actions it is UNCHANGED and its type
\* carries from the hypothesis IndTypeOk. `BY DEF Step, <actions>` unfolds Step's
\* disjunction and the cited actions; uncited disjuncts keep the variable via
\* their own UNCHANGED tuple. Message-adding actions build records that match the
\* IndTypeOk element sets (src in Corr\union Faulty, round = index, value typed).
THEOREM TypePres ==
  ASSUME TypedIndInvMin, Step
  PROVE  IndTypeOk'
  <1> USE DEF TypedIndInvMin, IndTypeOk
  <1>1. (round \in [Corr -> (0)..(MaxRound)])'
        BY DEF Step, UponQuorumOfPrecommitsAny, OnRoundCatchup
  <1>2. (step \in [Corr -> {"PROPOSE_OF_STEP", "PREVOTE_OF_STEP", "PRECOMMIT_OF_STEP", "DECIDED_OF_STEP"}])'
        BY SMT DEF Step, UponProposalInPropose, UponProposalInProposeAndPrevote,
            UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
            UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
            OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup
  <1>3. (decision \in [Corr -> (ValidValues \union {-1})])'
        BY DEF Step, UponProposalInPrecommitNoDecision
  <1>4. (locked_value \in [Corr -> (ValidValues \union {-1})])'
        BY SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote
  <1>5. (locked_round \in [Corr -> ((0)..(MaxRound) \union {-1})])'
        BY SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote
  <1>6. (valid_value \in [Corr -> (ValidValues \union {-1})])'
        BY DEF Step, UponProposalInPrevoteOrCommitAndPrevote
  <1>7. (valid_round \in [Corr -> ((0)..(MaxRound) \union {-1})])'
        BY SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote
  <1>8. (DOMAIN msgs_propose = (0)..(MaxRound))'
        BY SMT DEF Step, InsertProposal, FaultyStep
  <1>9. (\A v_v89 \in (0)..(MaxRound): \A v_v90 \in msgs_propose[v_v89]: (v_v90 \in {[proposal |-> v_v91[3], round |-> v_v91[2], src |-> v_v91[1], valid_round |-> v_v91[4]]: v_v91 \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1})) \X (((0)..(MaxRound) \union {-1}))}))'
    <2> DEFINE RecP == {[proposal |-> t[3], round |-> t[2], src |-> t[1], valid_round |-> t[4]]: t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1})) \X (((0)..(MaxRound) \union {-1}))}
    <2> SUFFICES ASSUME NEW r \in (0)..(MaxRound), NEW m \in msgs_propose'[r]
                 PROVE  m \in RecP
        OBVIOUS
    <2>H. \A mm \in msgs_propose[r] : mm \in RecP
        BY DEF IndTypeOk
    <2>sel. msgs_propose' = msgs_propose \/ (\E p \in Corr : InsertProposal(p)) \/ FaultyStep
        BY DEF Step
    <2>1. CASE msgs_propose' = msgs_propose
        BY <2>H, <2>1
    <2>2. CASE \E p \in Corr : InsertProposal(p)
        <3> PICK p \in Corr : InsertProposal(p)  BY <2>2
        <3>1. PICK v \in ValidValues :
                msgs_propose' = [msgs_propose EXCEPT ![round[p]] =
                  (msgs_propose[round[p]] \union {[proposal |-> (IF (valid_value[p] /= -1) THEN valid_value[p] ELSE v),
                     round |-> round[p], src |-> p, valid_round |-> valid_round[p]]})]
              BY DEF InsertProposal
        <3>2. round[p] \in (0)..(MaxRound) /\ valid_round[p] \in ((0)..(MaxRound) \union {-1})
              /\ valid_value[p] \in (ValidValues \union {-1})
              BY DEF IndTypeOk
        <3>3. (IF (valid_value[p] /= -1) THEN valid_value[p] ELSE v) \in ((ValidValues \union InvalidValues) \union {-1})
              BY <3>2
        <3>4. m \in msgs_propose[r]
              \/ m = [proposal |-> (IF (valid_value[p] /= -1) THEN valid_value[p] ELSE v), round |-> round[p], src |-> p, valid_round |-> valid_round[p]]
              BY <3>1
        <3>5. CASE m \in msgs_propose[r]  BY <2>H, <3>5
        <3>6. CASE m = [proposal |-> (IF (valid_value[p] /= -1) THEN valid_value[p] ELSE v), round |-> round[p], src |-> p, valid_round |-> valid_round[p]]
              BY <3>2, <3>3, <3>6, ProposeRecTyped
        <3> QED  BY <3>4, <3>5, <3>6
    <2>3. CASE FaultyStep
        <3>1. PICK rF \in (0)..(MaxRound), fps1 \in SUBSET Faulty,
                   v1 \in (ValidValues \union InvalidValues), vr1 \in ((0)..(MaxRound) \union {-1}) :
                msgs_propose' = [msgs_propose EXCEPT ![rF] =
                  (msgs_propose[rF] \union {[proposal |-> v1, round |-> rF, src |-> v_v53, valid_round |-> vr1] : v_v53 \in fps1})]
              BY <2>3 DEF FaultyStep
        <3>2. m \in msgs_propose[r]
              \/ (\E s0 \in fps1 : m = [proposal |-> v1, round |-> rF, src |-> s0, valid_round |-> vr1])
              BY <3>1
        <3>3. CASE m \in msgs_propose[r]  BY <2>H, <3>3
        <3>4. CASE \E s0 \in fps1 : m = [proposal |-> v1, round |-> rF, src |-> s0, valid_round |-> vr1]
              <4> PICK s0 \in fps1 : m = [proposal |-> v1, round |-> rF, src |-> s0, valid_round |-> vr1]  BY <3>4
              <4>1. s0 \in (Corr \union Faulty)  BY <3>4
              <4>2. v1 \in ((ValidValues \union InvalidValues) \union {-1})  OBVIOUS
              <4> QED  BY <4>1, <4>2, ProposeRecTyped
        <3> QED  BY <3>2, <3>3, <3>4
    <2> QED  BY <2>sel, <2>1, <2>2, <2>3
  <1>10. (\A v_v92 \in DOMAIN msgs_propose: \A v_v93 \in msgs_propose[v_v92]: (v_v92 = v_v93.round))'
        BY SMT DEF Step, InsertProposal, FaultyStep
  <1>11. (DOMAIN msgs_prevote = (0)..(MaxRound))'
        BY SMT DEF Step, UponProposalInPropose, UponProposalInProposeAndPrevote, OnTimeoutPropose, FaultyStep
  <1>12. (\A v_v94 \in (0)..(MaxRound): \A v_v95 \in msgs_prevote[v_v94]: (v_v95 \in {[id |-> v_v96[3], kind |-> "PREVOTE_OF_VOTEKIND", round |-> v_v96[2], src |-> v_v96[1]]: v_v96 \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}))'
    <2> DEFINE RecV == {[id |-> t[3], kind |-> "PREVOTE_OF_VOTEKIND", round |-> t[2], src |-> t[1]]: t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
    <2> SUFFICES ASSUME NEW r \in (0)..(MaxRound), NEW m \in msgs_prevote'[r]
                 PROVE  m \in RecV
        OBVIOUS
    <2>H. \A mm \in msgs_prevote[r] : mm \in RecV  BY DEF IndTypeOk
    \* one lemma shape covers all three correct broadcasts: some in-range id is appended for p
    <2>corr. ASSUME NEW p \in Corr,
                    \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                      msgs_prevote' = [msgs_prevote EXCEPT ![round[p]] =
                        (msgs_prevote[round[p]] \union {[id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
             PROVE  m \in RecV
        <3> PICK idv \in ((ValidValues \union InvalidValues) \union {-1}) :
              msgs_prevote' = [msgs_prevote EXCEPT ![round[p]] =
                (msgs_prevote[round[p]] \union {[id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
            BY <2>corr
        <3>1. round[p] \in (0)..(MaxRound)  BY DEF IndTypeOk
        <3>2. m \in msgs_prevote[r] \/ m = [id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]  OBVIOUS
        <3>3. CASE m \in msgs_prevote[r]  BY <2>H, <3>3
        <3>4. CASE m = [id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]
              BY <3>1, <3>4, PrevoteRecTyped
        <3> QED  BY <3>2, <3>3, <3>4
    <2>sel. \/ msgs_prevote' = msgs_prevote
            \/ \E p \in Corr : UponProposalInPropose(p)
            \/ \E p \in Corr : UponProposalInProposeAndPrevote(p)
            \/ \E p \in Corr : OnTimeoutPropose(p)
            \/ FaultyStep
        BY DEF Step
    <2>1. CASE msgs_prevote' = msgs_prevote  BY <2>H, <2>1
    <2>2. CASE \E p \in Corr : UponProposalInPropose(p)
        <3> PICK p \in Corr : UponProposalInPropose(p)  BY <2>2
        <3>a. \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                msgs_prevote' = [msgs_prevote EXCEPT ![round[p]] =
                  (msgs_prevote[round[p]] \union {[id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY DEF UponProposalInPropose
        <3> QED  BY <3>a, <2>corr
    <2>3. CASE \E p \in Corr : UponProposalInProposeAndPrevote(p)
        <3> PICK p \in Corr : UponProposalInProposeAndPrevote(p)  BY <2>3
        <3>a. \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                msgs_prevote' = [msgs_prevote EXCEPT ![round[p]] =
                  (msgs_prevote[round[p]] \union {[id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY DEF UponProposalInProposeAndPrevote
        <3> QED  BY <3>a, <2>corr
    <2>4. CASE \E p \in Corr : OnTimeoutPropose(p)
        <3> PICK p \in Corr : OnTimeoutPropose(p)  BY <2>4
        <3>a. \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                msgs_prevote' = [msgs_prevote EXCEPT ![round[p]] =
                  (msgs_prevote[round[p]] \union {[id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY DEF OnTimeoutPropose
        <3> QED  BY <3>a, <2>corr
    <2>5. CASE FaultyStep
        <3>1. PICK rF \in (0)..(MaxRound), fps2 \in SUBSET Faulty, v2 \in (ValidValues \union InvalidValues) :
                msgs_prevote' = [msgs_prevote EXCEPT ![rF] =
                  (msgs_prevote[rF] \union {[id |-> v2, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rF, src |-> v_v54] : v_v54 \in fps2})]
              BY <2>5 DEF FaultyStep
        <3>2. m \in msgs_prevote[r]
              \/ (\E s0 \in fps2 : m = [id |-> v2, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rF, src |-> s0])
              BY <3>1
        <3>3. CASE m \in msgs_prevote[r]  BY <2>H, <3>3
        <3>4. CASE \E s0 \in fps2 : m = [id |-> v2, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rF, src |-> s0]
              <4> PICK s0 \in fps2 : m = [id |-> v2, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rF, src |-> s0]  BY <3>4
              <4>1. s0 \in (Corr \union Faulty)  BY <3>4
              <4>2. v2 \in ((ValidValues \union InvalidValues) \union {-1})  OBVIOUS
              <4> QED  BY <4>1, <4>2, PrevoteRecTyped
        <3> QED  BY <3>2, <3>3, <3>4
    <2> QED  BY <2>sel, <2>1, <2>2, <2>3, <2>4, <2>5
  <1>13. (\A v_v97 \in DOMAIN msgs_prevote: \A v_v98 \in msgs_prevote[v_v97]: (v_v97 = v_v98.round))'
        BY SMT DEF Step, UponProposalInPropose, UponProposalInProposeAndPrevote, OnTimeoutPropose, FaultyStep
  <1>14. (DOMAIN msgs_precommit = (0)..(MaxRound))'
        BY SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote, UponQuorumOfPrevotesAny, OnQuorumOfNilPrevotes, FaultyStep
  <1>15. (\A v_v99 \in (0)..(MaxRound): \A v_v100 \in msgs_precommit[v_v99]: (v_v100 \in {[id |-> v_v101[3], kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> v_v101[2], src |-> v_v101[1]]: v_v101 \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}))'
    <2> DEFINE RecC == {[id |-> t[3], kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> t[2], src |-> t[1]]: t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
    <2> SUFFICES ASSUME NEW r \in (0)..(MaxRound), NEW m \in msgs_precommit'[r]
                 PROVE  m \in RecC
        BY SMT
    <2>H. \A mm \in msgs_precommit[r] : mm \in RecC  BY DEF IndTypeOk
    <2>corr. ASSUME NEW p \in Corr,
                    \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                      msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                        (msgs_precommit[round[p]] \union {[id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
             PROVE  m \in RecC
        <3> PICK idv \in ((ValidValues \union InvalidValues) \union {-1}) :
              msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                (msgs_precommit[round[p]] \union {[id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
            BY <2>corr
        <3>1. round[p] \in (0)..(MaxRound)  BY DEF IndTypeOk
        <3>2. m \in msgs_precommit[r] \/ m = [id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]  OBVIOUS
        <3>3. CASE m \in msgs_precommit[r]  BY <2>H, <3>3
        <3>4. CASE m = [id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
              BY <3>1, <3>4, PrecommitRecTyped
        <3> QED  BY <3>2, <3>3, <3>4
    <2>sel. \/ msgs_precommit' = msgs_precommit
            \/ \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
            \/ \E p \in Corr : UponQuorumOfPrevotesAny(p)
            \/ \E p \in Corr : OnQuorumOfNilPrevotes(p)
            \/ FaultyStep
        BY DEF Step
    <2>1. CASE msgs_precommit' = msgs_precommit  BY <2>H, <2>1
    <2>2. CASE \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
        <3> PICK p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)  BY <2>2
        <3>a. \/ msgs_precommit' = msgs_precommit
              \/ \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                   msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                     (msgs_precommit[round[p]] \union {[id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY DEF UponProposalInPrevoteOrCommitAndPrevote
        <3>b. CASE msgs_precommit' = msgs_precommit  BY <2>H, <3>b
        <3>c. CASE \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                     msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                       (msgs_precommit[round[p]] \union {[id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY <3>c, <2>corr
        <3> QED  BY <3>a, <3>b, <3>c
    <2>3. CASE \E p \in Corr : UponQuorumOfPrevotesAny(p)
        <3> PICK p \in Corr : UponQuorumOfPrevotesAny(p)  BY <2>3
        <3>a. \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                  (msgs_precommit[round[p]] \union {[id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY DEF UponQuorumOfPrevotesAny
        <3> QED  BY <3>a, <2>corr
    <2>4. CASE \E p \in Corr : OnQuorumOfNilPrevotes(p)
        <3> PICK p \in Corr : OnQuorumOfNilPrevotes(p)  BY <2>4
        <3>a. \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                  (msgs_precommit[round[p]] \union {[id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY DEF OnQuorumOfNilPrevotes
        <3> QED  BY <3>a, <2>corr
    <2>5. CASE FaultyStep
        <3>1. PICK rF \in (0)..(MaxRound), fps3 \in SUBSET Faulty, v3 \in (ValidValues \union InvalidValues) :
                msgs_precommit' = [msgs_precommit EXCEPT ![rF] =
                  (msgs_precommit[rF] \union {[id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> rF, src |-> v_v55] : v_v55 \in fps3})]
              BY <2>5 DEF FaultyStep
        <3>2. m \in msgs_precommit[r]
              \/ (\E s0 \in fps3 : m = [id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> rF, src |-> s0])
              BY <3>1
        <3>3. CASE m \in msgs_precommit[r]  BY <2>H, <3>3
        <3>4. CASE \E s0 \in fps3 : m = [id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> rF, src |-> s0]
              <4> PICK s0 \in fps3 : m = [id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> rF, src |-> s0]  BY <3>4
              <4>1. s0 \in (Corr \union Faulty)  BY <3>4
              <4>2. v3 \in ((ValidValues \union InvalidValues) \union {-1})  OBVIOUS
              <4> QED  BY <4>1, <4>2, PrecommitRecTyped
        <3> QED  BY <3>2, <3>3, <3>4
    <2> QED  BY <2>sel, <2>1, <2>2, <2>3, <2>4, <2>5
  <1>16. (\A v_v102 \in DOMAIN msgs_precommit: \A v_v103 \in msgs_precommit[v_v102]: (v_v102 = v_v103.round))'
        BY SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote, UponQuorumOfPrevotesAny, OnQuorumOfNilPrevotes, FaultyStep
  <1>17. (last_action \in {"INIT", "INSERT_PROPOSAL", "UPON_PROPOSAL_PROPOSE", "UPON_PROPOSAL_PROPOSE_AND_PREVOTE", "UPON_QUORUM_PREVOTES_ANY", "UPON_PROPOSAL_PREVOTE_OR_COMMIT_AND_PREVOTE", "UPON_QUORUM_PRECOMMITS_ANY", "UPON_PROPOSAL_PRECOMMIT_NO_DECISION", "ON_TIMEOUT_PROPOSE", "ON_QUORUM_NIL_PREVOTES", "ON_ROUND_CATCHUP"})'
        BY DEF Step, InsertProposal, UponProposalInPropose, UponProposalInProposeAndPrevote,
            UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
            UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
            OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup
  <1> QED
      BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
         <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17
      DEF IndTypeOk

\*****************************************************************************
\* SECTION C -- INDUCTIVE STEP
\*
\* The transition is `Step` (there is no [Step]_vars; this mirrors how Apalache
\* checks IndInit /\ Next => IndInv', with no explicit stutter case). `Step`
\* inlines the disjunction of the 10 correct sub-actions (each guarded by a
\* process p \in Corr and paired with its own UNCHANGED tuple) plus FaultyStep.
\*
\* For each IndInvMin conjunct C we prove an assembler
\*   Pres_C == ASSUME TypedIndInvMin, Step PROVE C'
\* by splitting Step into its 11 disjuncts and discharging each with a per-action
\* theorem Pres_C_<action>. Below, `AllValidAndLockedRoundBounded` is fully worked
\* out as the template; the remaining 16 assemblers are OMITTED stubs.
\*****************************************************************************

\* ---------------------------------------------------------------------------
\* WORKED CONJUNCT: AllValidAndLockedRoundBounded
\*   \A p \in Corr: valid_round[p] <= round[p] /\ locked_round[p] <= round[p]
\*
\* 8 actions leave round, valid_round, locked_round all UNCHANGED (trivial). The
\* 3 substantive actions touch round or the round flags:
\*   - UponProposalInPrevoteOrCommitAndPrevote sets valid_round[p]:=round[p] and
\*     (in the "then" branch) locked_round[p]:=round[p], with round UNCHANGED.
\*   - UponQuorumOfPrecommitsAny advances round[p]:=round[p]+1, flags UNCHANGED.
\*   - OnRoundCatchup jumps round[p] up to some rnd>round[p], flags UNCHANGED.
\* ---------------------------------------------------------------------------

\* --- 8 trivial (UNCHANGED) cases ---

THEOREM Pres_Bounded_InsertProposal ==
  ASSUME TypedIndInvMin, NEW p \in Corr, InsertProposal(p),
         UNCHANGED <<round, step, decision, locked_value, locked_round, valid_value, valid_round, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInvMin, IndInvMin, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_UponProposalInPropose ==
  ASSUME TypedIndInvMin, NEW p \in Corr, UponProposalInPropose(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInvMin, IndInvMin, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_UponProposalInProposeAndPrevote ==
  ASSUME TypedIndInvMin, NEW p \in Corr, UponProposalInProposeAndPrevote(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInvMin, IndInvMin, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_UponQuorumOfPrevotesAny ==
  ASSUME TypedIndInvMin, NEW p \in Corr, UponQuorumOfPrevotesAny(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInvMin, IndInvMin, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_UponProposalInPrecommitNoDecision ==
  ASSUME TypedIndInvMin, NEW p \in Corr, UponProposalInPrecommitNoDecision(p),
         UNCHANGED <<round, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInvMin, IndInvMin, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_OnTimeoutPropose ==
  ASSUME TypedIndInvMin, NEW p \in Corr, OnTimeoutPropose(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInvMin, IndInvMin, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_OnQuorumOfNilPrevotes ==
  ASSUME TypedIndInvMin, NEW p \in Corr, OnQuorumOfNilPrevotes(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInvMin, IndInvMin, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_Faulty ==
  ASSUME TypedIndInvMin, FaultyStep,
         UNCHANGED <<round, step, decision, locked_value, locked_round, valid_value, valid_round, last_action>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInvMin, IndInvMin, AllValidAndLockedRoundBounded

\* --- 3 substantive cases ---

\* Sets valid_round[p]:=round[p], and locked_round[p]:=round[p] in the "then"
\* branch (else locked_round UNCHANGED); round itself is UNCHANGED.
THEOREM Pres_Bounded_UponProposalInPrevoteOrCommitAndPrevote ==
  ASSUME TypedIndInvMin, NEW p \in Corr,
         UponProposalInPrevoteOrCommitAndPrevote(p),
         UNCHANGED <<round, decision, msgs_propose, msgs_prevote>>
  PROVE  AllValidAndLockedRoundBounded'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk, AllValidAndLockedRoundBounded
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  valid_round'[q] <= round'[q] /\ locked_round'[q] <= round'[q]
      OBVIOUS
  <1>1. round' = round
        OBVIOUS
  <1>2. valid_round' = [valid_round EXCEPT ![p] = round[p]]
        BY DEF UponProposalInPrevoteOrCommitAndPrevote
  <1>3. locked_round' = [locked_round EXCEPT ![p] = round[p]] \/ locked_round' = locked_round
        BY DEF UponProposalInPrevoteOrCommitAndPrevote
  <1>4. /\ DOMAIN round = Corr /\ DOMAIN valid_round = Corr /\ DOMAIN locked_round = Corr
        /\ round[p] \in Int /\ round[q] \in Int
        BY SMT DEF TypedIndInvMin, IndTypeOk
  <1>5. valid_round[q] <= round[q] /\ locked_round[q] <= round[q]
        OBVIOUS
  <1> QED
      BY <1>1, <1>2, <1>3, <1>4, <1>5, SMT

\* Advances round[p] to round[p]+1; valid_round and locked_round are UNCHANGED.
THEOREM Pres_Bounded_UponQuorumOfPrecommitsAny ==
  ASSUME TypedIndInvMin, NEW p \in Corr,
         UponQuorumOfPrecommitsAny(p),
         UNCHANGED <<decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk, AllValidAndLockedRoundBounded
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  valid_round'[q] <= round'[q] /\ locked_round'[q] <= round'[q]
      OBVIOUS
  <1>1. round' = [round EXCEPT ![p] = round[p] + 1]
        BY DEF UponQuorumOfPrecommitsAny
  <1>2. valid_round' = valid_round /\ locked_round' = locked_round
        BY SMT
  <1>3. /\ DOMAIN round = Corr
        /\ round[p] \in Int /\ round[q] \in Int
        BY SMT DEF TypedIndInvMin, IndTypeOk
  <1>4. valid_round[q] <= round[q] /\ locked_round[q] <= round[q]
        OBVIOUS
  <1> QED
      BY <1>1, <1>2, <1>3, <1>4, SMT

\* Jumps round[p] up to some rnd > round[p]; valid_round and locked_round UNCHANGED.
THEOREM Pres_Bounded_OnRoundCatchup ==
  ASSUME TypedIndInvMin, NEW p \in Corr,
         OnRoundCatchup(p),
         UNCHANGED <<decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk, AllValidAndLockedRoundBounded
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  valid_round'[q] <= round'[q] /\ locked_round'[q] <= round'[q]
      OBVIOUS
  <1>1. \E rnd \in (0)..(MaxRound) : rnd > round[p] /\ round' = [round EXCEPT ![p] = rnd]
        BY DEF OnRoundCatchup
  <1>2. valid_round' = valid_round /\ locked_round' = locked_round
        BY SMT
  <1>3. /\ DOMAIN round = Corr
        /\ round[p] \in Int /\ round[q] \in Int
        BY SMT DEF TypedIndInvMin, IndTypeOk
  <1>4. valid_round[q] <= round[q] /\ locked_round[q] <= round[q]
        OBVIOUS
  <1> QED
      BY <1>1, <1>2, <1>3, <1>4, SMT

\* Assembler: split Step into its 11 disjuncts.
THEOREM Pres_AllValidAndLockedRoundBounded ==
  ASSUME TypedIndInvMin, Step
  PROVE  AllValidAndLockedRoundBounded'
  BY Pres_Bounded_InsertProposal,
     Pres_Bounded_UponProposalInPropose,
     Pres_Bounded_UponProposalInProposeAndPrevote,
     Pres_Bounded_UponQuorumOfPrevotesAny,
     Pres_Bounded_UponProposalInPrevoteOrCommitAndPrevote,
     Pres_Bounded_UponQuorumOfPrecommitsAny,
     Pres_Bounded_UponProposalInPrecommitNoDecision,
     Pres_Bounded_OnTimeoutPropose,
     Pres_Bounded_OnQuorumOfNilPrevotes,
     Pres_Bounded_OnRoundCatchup,
     Pres_Bounded_Faulty
  DEF Step

\* ---------------------------------------------------------------------------
\* REMAINING 16 CONJUNCT ASSEMBLERS (OMITTED stubs).
\* Each follows the pattern above: decompose into Pres_<Conj>_<action> theorems
\* over the 11 Step disjuncts, then assemble BY ... DEF Step.
\* ---------------------------------------------------------------------------

THEOREM Pres_AllNoFutureMessagesSent ==
  ASSUME TypedIndInvMin, Step PROVE AllNoFutureMessagesSent'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  /\ /\ \/ q = Proposer[round'[q]]
                         \/ \A mp \in msgs_propose'[round'[q]] : q # mp.src
                      /\ \/ step'[q] = "PREVOTE_OF_STEP"
                         \/ step'[q] = "PRECOMMIT_OF_STEP"
                         \/ step'[q] = "DECIDED_OF_STEP"
                         \/ \A mv \in msgs_prevote'[round'[q]] : q # mv.src
                      /\ \/ step'[q] = "PRECOMMIT_OF_STEP"
                         \/ step'[q] = "DECIDED_OF_STEP"
                         \/ \A mc \in msgs_precommit'[round'[q]] : q # mc.src
                      /\ \A rr \in {r \in (0)..(MaxRound) : r > round'[q]} :
                           /\ \A mp \in msgs_propose'[rr] : q # mp.src
                           /\ \A mv \in msgs_prevote'[rr] : q # mv.src
                           /\ \A mc \in msgs_precommit'[rr] : q # mc.src
      BY DEF AllNoFutureMessagesSent
  \* The selector carries, for each case that needs it, the frame equalities from that
  \* Step branch's UNCHANGED tuple. The bare action alone does NOT determine the frame
  \* (e.g. FaultyStep with an empty faulty injection can co-occur with OnRoundCatchup,
  \* which changes round), so the frame must come from the branch, not the action.
  <1>sel. \/ (FaultyStep /\ round' = round /\ step' = step)
           \/ ((\E p \in Corr : InsertProposal(p))
                 /\ round' = round /\ step' = step
                 /\ msgs_prevote' = msgs_prevote /\ msgs_precommit' = msgs_precommit)
           \/ \E p \in Corr : UponProposalInPropose(p)
           \/ \E p \in Corr : UponProposalInProposeAndPrevote(p)
           \/ \E p \in Corr : UponQuorumOfPrevotesAny(p)
           \/ ((\E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p))
                 /\ round' = round
                 /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote)
           \/ \E p \in Corr : UponQuorumOfPrecommitsAny(p)
           \/ ((\E p \in Corr : UponProposalInPrecommitNoDecision(p))
                 /\ round' = round
                 /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote
                 /\ msgs_precommit' = msgs_precommit)
           \/ \E p \in Corr : OnTimeoutPropose(p)
           \/ \E p \in Corr : OnQuorumOfNilPrevotes(p)
           \/ \E p \in Corr : OnRoundCatchup(p)
      BY DEF Step
  <1>faulty. CASE FaultyStep /\ round' = round /\ step' = step
      <2>frame. round' = round /\ step' = step
            BY <1>faulty
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>faulty, <2>frame, <2>old, DisjointCF, SMT DEF FaultyStep
  <1>insert. CASE (\E p \in Corr : InsertProposal(p))
                  /\ round' = round /\ step' = step
                  /\ msgs_prevote' = msgs_prevote /\ msgs_precommit' = msgs_precommit
      <2> PICK p \in Corr : InsertProposal(p) BY <1>insert
      <2>frame. /\ round' = round
                /\ step' = step
                /\ msgs_prevote' = msgs_prevote
                /\ msgs_precommit' = msgs_precommit
            BY <1>insert
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>insert, <2>frame, <2>old, SMT DEF InsertProposal
  <1>proposal. CASE \E p \in Corr : UponProposalInPropose(p)
      <2> PICK p \in Corr : UponProposalInPropose(p) BY <1>proposal
      <2> QED BY <1>proposal, DisjointCF, SMT DEF AllNoFutureMessagesSent, Step,
         UponProposalInPropose
  <1>proposalPrevote. CASE \E p \in Corr : UponProposalInProposeAndPrevote(p)
      <2> PICK p \in Corr : UponProposalInProposeAndPrevote(p) BY <1>proposalPrevote
      <2> QED BY <1>proposalPrevote, DisjointCF, SMT DEF AllNoFutureMessagesSent, Step,
         UponProposalInProposeAndPrevote
  <1>quorumPrevotes. CASE \E p \in Corr : UponQuorumOfPrevotesAny(p)
      <2> PICK p \in Corr : UponQuorumOfPrevotesAny(p) BY <1>quorumPrevotes
      <2> QED BY <1>quorumPrevotes, DisjointCF, SMT DEF AllNoFutureMessagesSent, Step,
         UponQuorumOfPrevotesAny
  <1>proposalPrevoteCommit. CASE (\E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p))
                                 /\ round' = round
                                 /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote
      <2> PICK p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p) BY <1>proposalPrevoteCommit
      <2>frame. /\ round' = round
                /\ msgs_propose' = msgs_propose
                /\ msgs_prevote' = msgs_prevote
            BY <1>proposalPrevoteCommit
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>proposalPrevoteCommit, <2>frame, <2>old, DisjointCF, SMT
         DEF UponProposalInPrevoteOrCommitAndPrevote
  <1>quorumPrecommits. CASE \E p \in Corr : UponQuorumOfPrecommitsAny(p)
      <2> PICK p \in Corr : UponQuorumOfPrecommitsAny(p) BY <1>quorumPrecommits
      <2> QED BY <1>quorumPrecommits, DisjointCF, SMT DEF AllNoFutureMessagesSent, Step,
         UponQuorumOfPrecommitsAny
  <1>decide. CASE (\E p \in Corr : UponProposalInPrecommitNoDecision(p))
                  /\ round' = round
                  /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote
                  /\ msgs_precommit' = msgs_precommit
      <2> PICK p \in Corr : UponProposalInPrecommitNoDecision(p) BY <1>decide
      <2>frame. /\ round' = round
                /\ msgs_propose' = msgs_propose
                /\ msgs_prevote' = msgs_prevote
                /\ msgs_precommit' = msgs_precommit
            BY <1>decide
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>decide, <2>frame, <2>old, SMT
         DEF UponProposalInPrecommitNoDecision
  <1>timeoutPropose. CASE \E p \in Corr : OnTimeoutPropose(p)
      <2> PICK p \in Corr : OnTimeoutPropose(p) BY <1>timeoutPropose
      <2> QED BY <1>timeoutPropose, DisjointCF, SMT DEF AllNoFutureMessagesSent, Step,
         OnTimeoutPropose
  <1>nilPrevotes. CASE \E p \in Corr : OnQuorumOfNilPrevotes(p)
      <2> PICK p \in Corr : OnQuorumOfNilPrevotes(p) BY <1>nilPrevotes
      <2> QED BY <1>nilPrevotes, DisjointCF, SMT DEF AllNoFutureMessagesSent, Step,
         OnQuorumOfNilPrevotes
  <1>roundCatchup. CASE \E p \in Corr : OnRoundCatchup(p)
      <2> PICK p \in Corr : OnRoundCatchup(p) BY <1>roundCatchup
      <2> QED BY <1>roundCatchup, DisjointCF, SMT DEF AllNoFutureMessagesSent, Step,
         OnRoundCatchup
  <1> QED BY <1>sel, <1>faulty, <1>insert, <1>proposal, <1>proposalPrevote,
     <1>quorumPrevotes, <1>proposalPrevoteCommit, <1>quorumPrecommits,
     <1>decide, <1>timeoutPropose, <1>nilPrevotes, <1>roundCatchup

THEOREM Pres_AllIfInPrevoteThenSentPrevote ==
  ASSUME TypedIndInvMin, Step PROVE AllIfInPrevoteThenSentPrevote'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, step'[q] = "PREVOTE_OF_STEP"
               PROVE  \E m \in msgs_prevote'[round'[q]] :
                         /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
                         /\ q = m.src
      BY DEF AllIfInPrevoteThenSentPrevote
  <1>1. CASE step[q] = "PREVOTE_OF_STEP"
      <2>0. round'[q] = round[q]
            BY <1>1, SMT DEF Step, UponQuorumOfPrevotesAny,
               UponProposalInPrevoteOrCommitAndPrevote, UponQuorumOfPrecommitsAny,
               OnQuorumOfNilPrevotes, OnRoundCatchup
      <2>1. PICK m \in msgs_prevote[round[q]] :
                /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
                /\ q = m.src
            BY <1>1 DEF AllIfInPrevoteThenSentPrevote
      <2>2. m \in msgs_prevote'[round'[q]]
            BY <2>0, <2>1, PrevoteMonotone
      <2> QED BY <2>1, <2>2
  <1>2. CASE step[q] # "PREVOTE_OF_STEP"
      <2> QED BY <1>2, EnteredPrevoteHasSentPrevote
  <1> QED BY <1>1, <1>2

THEOREM Pres_AllIfInPrecommitThenSentPrecommit ==
  ASSUME TypedIndInvMin, Step PROVE AllIfInPrecommitThenSentPrecommit'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, step'[q] = "PRECOMMIT_OF_STEP"
               PROVE  \E m \in msgs_precommit'[round'[q]] :
                         /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
                         /\ q = m.src
      BY DEF AllIfInPrecommitThenSentPrecommit
  <1>1. CASE step[q] = "PRECOMMIT_OF_STEP"
      <2>0. round'[q] = round[q]
            BY <1>1, SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
               OnRoundCatchup
      <2>1. PICK m \in msgs_precommit[round[q]] :
                /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
                /\ q = m.src
            BY <1>1 DEF AllIfInPrecommitThenSentPrecommit
      <2>2. m \in msgs_precommit'[round'[q]]
            BY <2>0, <2>1, PrecommitMonotone
      <2> QED BY <2>1, <2>2
  <1>2. CASE step[q] # "PRECOMMIT_OF_STEP"
      <2> QED BY <1>2, EnteredPrecommitHasSentPrecommit
  <1> QED BY <1>1, <1>2

\* A decided process received a matching proposal (at some round). Only
\* UponProposalInPrecommitNoDecision decides, and its guard exhibits the proposal;
\* an already-decided process keeps its decision (it cannot act) and the proposal
\* persists by ProposeMonotone.
THEOREM Pres_AllIfInDecidedThenReceivedProposal ==
  ASSUME TypedIndInvMin, Step
  PROVE  AllIfInDecidedThenReceivedProposal'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, step'[q] = "DECIDED_OF_STEP"
               PROVE  \E rr \in (0)..(MaxRound) : \E mm \in msgs_propose'[rr] :
                        mm.src = Proposer[rr] /\ mm.proposal = decision'[q]
      BY DEF AllIfInDecidedThenReceivedProposal
  <1>1. CASE step[q] = "DECIDED_OF_STEP"
      <2>0. decision[q] \in ValidValues
            BY <1>1 DEF AllIfInDecidedThenValidDecision
      <2>00. decision[q] # -1
            BY <2>0, NilNotValid
      <2>1. decision'[q] = decision[q]
            BY <2>00, SMT DEF Step, UponProposalInPrecommitNoDecision
      <2>2. PICK rr \in (0)..(MaxRound) : \E mm \in msgs_propose[rr] :
              mm.src = Proposer[rr] /\ mm.proposal = decision[q]
            BY <1>1 DEF AllIfInDecidedThenReceivedProposal
      <2>3. PICK mm \in msgs_propose[rr] : mm.src = Proposer[rr] /\ mm.proposal = decision[q]
            BY <2>2
      <2>4. mm \in msgs_propose'[rr]  BY <2>3, ProposeMonotone
      <2> QED  BY <2>1, <2>3, <2>4
  <1>2. CASE step[q] # "DECIDED_OF_STEP"
      <2>0. step'[q] # step[q]
            BY <1>2
      <2>a. \/ UponProposalInPropose(q) \/ UponProposalInProposeAndPrevote(q)
             \/ UponQuorumOfPrevotesAny(q) \/ UponProposalInPrevoteOrCommitAndPrevote(q)
             \/ UponQuorumOfPrecommitsAny(q) \/ UponProposalInPrecommitNoDecision(q)
             \/ OnTimeoutPropose(q) \/ OnQuorumOfNilPrevotes(q) \/ OnRoundCatchup(q)
            BY <2>0, StepChangeChar
      <2>1. UponProposalInPrecommitNoDecision(q)
            BY <2>a, SMT DEF UponProposalInPropose, UponProposalInProposeAndPrevote,
               UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
               OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup
      <2>2. PICK v \in ValidValues, rnd \in (0)..(MaxRound), vr \in ((0)..(MaxRound) \union {-1}) :
              /\ [proposal |-> v, round |-> rnd, src |-> Proposer[rnd], valid_round |-> vr] \in msgs_propose[rnd]
              /\ decision' = [decision EXCEPT ![q] = v]
            BY <2>1 DEF UponProposalInPrecommitNoDecision
      <2>3. decision'[q] = v  BY <2>2
      <2>4. [proposal |-> v, round |-> rnd, src |-> Proposer[rnd], valid_round |-> vr] \in msgs_propose'[rnd]
            BY <2>2, ProposeMonotone
      <2> QED  BY <2>2, <2>3, <2>4
  <1> QED  BY <1>1, <1>2

THEOREM Pres_AllIfInDecidedThenReceivedTwoThirds ==
  ASSUME TypedIndInvMin, Step PROVE AllIfInDecidedThenReceivedTwoThirds'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, step'[q] = "DECIDED_OF_STEP"
               PROVE  \E rr \in (0)..(MaxRound) :
                         Cardinality({s \in (Corr \union Faulty) :
                           \E m \in {mm \in msgs_precommit'[rr] :
                             mm.id = decision'[q]} : s = m.src})
                         >= ((2 * T) + 1)
      BY DEF AllIfInDecidedThenReceivedTwoThirds
  <1>1. CASE step[q] = "DECIDED_OF_STEP"
      <2>0. decision[q] \in ValidValues
            BY <1>1 DEF AllIfInDecidedThenValidDecision
      <2>00. decision[q] # -1
            BY <2>0, NilNotValid
      <2>1. decision'[q] = decision[q]
            BY <2>00, SMT DEF Step, UponProposalInPrecommitNoDecision
      <2>2. PICK rr \in (0)..(MaxRound) :
                Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit[rr] :
                    mm.id = decision[q]} : s = m.src})
                >= ((2 * T) + 1)
            BY <1>1 DEF AllIfInDecidedThenReceivedTwoThirds
      <2>3. decision[q] \in ((ValidValues \union InvalidValues) \union {-1})
            BY <2>0
      <2>4. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit[rr] :
                    mm.id = decision[q]} : s = m.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit'[rr] :
                    mm.id = decision[q]} : s = m.src})
            BY <2>2, <2>3, PrecommitSenderSetCardinalityMonotone
      <2>5. /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_precommit[rr] :
                      mm.id = decision[q]} : s = m.src}) \in Int
              /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_precommit'[rr] :
                      mm.id = decision[q]} : s = m.src}) \in Int
              /\ ((2 * T) + 1) \in Int
            BY FiniteCF, FS_Union, FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>6. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit'[rr] :
                    mm.id = decision[q]} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>2, <2>4, <2>5, IntLeGeTrans1
      <2>7. {s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_precommit'[rr] :
                  mm.id = decision'[q]} : s = m.src}
              =
              {s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_precommit'[rr] :
                  mm.id = decision[q]} : s = m.src}
            BY <2>1, SMT
      <2> QED BY <2>2, <2>6, <2>7
  <1>2. CASE step[q] # "DECIDED_OF_STEP"
      <2>0. step'[q] # step[q]
            BY <1>2
      <2>a. \/ UponProposalInPropose(q) \/ UponProposalInProposeAndPrevote(q)
             \/ UponQuorumOfPrevotesAny(q) \/ UponProposalInPrevoteOrCommitAndPrevote(q)
             \/ UponQuorumOfPrecommitsAny(q) \/ UponProposalInPrecommitNoDecision(q)
             \/ OnTimeoutPropose(q) \/ OnQuorumOfNilPrevotes(q) \/ OnRoundCatchup(q)
            BY <2>0, StepChangeChar
      <2>1. UponProposalInPrecommitNoDecision(q)
            BY <1>2, <2>a, SMT DEF UponProposalInPropose, UponProposalInProposeAndPrevote,
               UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
               OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup
      <2>2. PICK v \in ValidValues, rnd \in (0)..(MaxRound), vr \in ((0)..(MaxRound) \union {-1}) :
                /\ Cardinality({m \in msgs_precommit[rnd] : v = m.id}) >= ((2 * T) + 1)
                /\ decision' = [decision EXCEPT ![q] = v]
            BY <2>1 DEF UponProposalInPrecommitNoDecision
      <2>3. decision'[q] = v
            BY <2>2
      <2>4. v \in ((ValidValues \union InvalidValues) \union {-1})
            BY <2>2
      <2>4b. {m \in msgs_precommit[rnd] : m.id = v}
              =
              {m \in msgs_precommit[rnd] : v = m.id}
            BY SMT
      <2>4c. Cardinality({m \in msgs_precommit[rnd] : m.id = v}) >= ((2 * T) + 1)
            BY <2>2, <2>4b
      <2>5. Cardinality({m \in msgs_precommit[rnd] : m.id = v})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_precommit[rnd] : mm.id = v} : s = m.src})
            BY <2>2, <2>4, PrecommitValueMessagesCardinalityLeSenders
      <2>6. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit[rnd] : mm.id = v} : s = m.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit'[rnd] : mm.id = v} : s = m.src})
            BY <2>2, <2>4, PrecommitSenderSetCardinalityMonotone
      <2>7. /\ Cardinality({m \in msgs_precommit[rnd] : m.id = v}) \in Int
              /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_precommit[rnd] : mm.id = v} : s = m.src}) \in Int
              /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_precommit'[rnd] : mm.id = v} : s = m.src}) \in Int
              /\ ((2 * T) + 1) \in Int
            BY <2>2, <2>4, PrecommitValueMessagesFinite, FiniteCF, FS_Union,
               FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>8. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit[rnd] : mm.id = v} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>4c, <2>5, <2>7, IntLeGeTrans1
      <2>9. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit'[rnd] : mm.id = v} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>6, <2>7, <2>8, IntLeGeTrans1
      <2>10. {s \in (Corr \union Faulty) :
                 \E m \in {mm \in msgs_precommit'[rnd] :
                   mm.id = decision'[q]} : s = m.src}
              =
              {s \in (Corr \union Faulty) :
                 \E m \in {mm \in msgs_precommit'[rnd] :
                   mm.id = v} : s = m.src}
            BY <2>3, SMT
      <2> QED BY <2>2, <2>9, <2>10
  <1> QED BY <1>1, <1>2

\* (step[p]=DECIDED) <=> (decision[p] in ValidValues). Only
\* UponProposalInPrecommitNoDecision sets step:=DECIDED, and it simultaneously
\* sets decision:=v with v in ValidValues. Every other step-changing action is
\* guarded by step[p] /= DECIDED and sets step to a non-DECIDED value while
\* leaving decision unchanged, so the old biconditional carries: the guard makes
\* the old LHS false, hence decision[p] was not a ValidValue.
THEOREM Pres_AllIfInDecidedThenValidDecision ==
  ASSUME TypedIndInvMin, Step
  PROVE  AllIfInDecidedThenValidDecision'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk, AllIfInDecidedThenValidDecision
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  (step'[q] = "DECIDED_OF_STEP") = (decision'[q] \in ValidValues)
      OBVIOUS
  <1> QED
      BY NilNotValid, SMT
      DEF Step, UponProposalInPropose, UponProposalInProposeAndPrevote,
          UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
          UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
          OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup

\* Only UponProposalInPrevoteOrCommitAndPrevote touches locked_round/locked_value:
\* its "then" branch sets locked_value[p]:=v (v in ValidValues, so /= -1) and
\* locked_round[p]:=round[p] (in 0..MaxRound, so /= -1) together; every other
\* action leaves both UNCHANGED. So the -1 flags stay in agreement.
THEOREM Pres_AllLockedRoundIffLockedValue ==
  ASSUME TypedIndInvMin, Step
  PROVE  AllLockedRoundIffLockedValue'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk, AllLockedRoundIffLockedValue
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  (locked_round'[q] = -1) = (locked_value'[q] = -1)
      OBVIOUS
  <1> QED
      BY NilNotValid, SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote

\* Symmetric to the above: only UponProposalInPrevoteOrCommitAndPrevote sets
\* valid_value[p]:=v (/= -1) and valid_round[p]:=round[p] (/= -1) together.
THEOREM Pres_AllValidRoundIffValidValue ==
  ASSUME TypedIndInvMin, Step
  PROVE  AllValidRoundIffValidValue'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk, AllValidRoundIffValidValue
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  (valid_round'[q] = -1) = (valid_value'[q] = -1)
      OBVIOUS
  <1> QED
      BY NilNotValid, SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote

THEOREM Pres_AllIfValidRoundThenTwoThirdsPrevotes ==
  ASSUME TypedIndInvMin, Step PROVE AllIfValidRoundThenTwoThirdsPrevotes'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, valid_round'[q] # -1
               PROVE  Cardinality({s \in (Corr \union Faulty) :
                         \E m \in {mm \in msgs_prevote'[valid_round'[q]] :
                           mm.id = valid_value'[q]} : s = m.src})
                       >= ((2 * T) + 1)
      BY DEF AllIfValidRoundThenTwoThirdsPrevotes
  <1>1. CASE valid_round'[q] = valid_round[q] /\ valid_value'[q] = valid_value[q]
      <2>0. valid_round[q] # -1
            BY <1>1
      <2>00. valid_round[q] \in (0)..(MaxRound)
            BY <2>0, SMT DEF IndTypeOk
      <2>1. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote[valid_round[q]] : mm.id = valid_value[q]} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>0 DEF AllIfValidRoundThenTwoThirdsPrevotes
      <2>2. valid_value[q] \in ((ValidValues \union InvalidValues) \union {-1})
            BY SMT DEF IndTypeOk
      <2>3. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote[valid_round[q]] : mm.id = valid_value[q]} : s = m.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote'[valid_round[q]] : mm.id = valid_value[q]} : s = m.src})
            BY <2>00, <2>2, PrevoteSenderSetCardinalityMonotone
      <2>4. valid_round'[q] = valid_round[q] /\ valid_value'[q] = valid_value[q]
            BY <1>1
      <2>5. /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_prevote[valid_round[q]] : mm.id = valid_value[q]} : s = m.src}) \in Int
              /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_prevote'[valid_round[q]] : mm.id = valid_value[q]} : s = m.src}) \in Int
              /\ ((2 * T) + 1) \in Int
            BY FiniteCF, FS_Union, FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>6. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote'[valid_round[q]] : mm.id = valid_value[q]} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>1, <2>3, <2>5, IntLeGeTrans1
      <2>7. {s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_prevote'[valid_round'[q]] : mm.id = valid_value'[q]} : s = m.src}
              =
              {s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_prevote'[valid_round[q]] : mm.id = valid_value[q]} : s = m.src}
            BY <2>4, SMT
      <2>8. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote'[valid_round'[q]] : mm.id = valid_value'[q]} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>6, <2>7
      <2> QED BY <2>8
  <1>2. CASE valid_round'[q] # valid_round[q] \/ valid_value'[q] # valid_value[q]
      <2>1. UponProposalInPrevoteOrCommitAndPrevote(q)
            BY <1>2, SMT DEF Step, InsertProposal, UponProposalInPropose,
               UponProposalInProposeAndPrevote, UponQuorumOfPrevotesAny,
               UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
               OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup, FaultyStep
      <2>2. PICK v \in ValidValues, vr \in ((0)..(MaxRound) \union {-1}) :
                /\ Cardinality({m \in msgs_prevote[round[q]] : m.id = v}) >= ((2 * T) + 1)
                /\ valid_value' = [valid_value EXCEPT ![q] = v]
                /\ valid_round' = [valid_round EXCEPT ![q] = round[q]]
            BY <2>1 DEF UponProposalInPrevoteOrCommitAndPrevote
      <2>3. valid_value'[q] = v /\ valid_round'[q] = round[q]
            BY <2>2, SMT DEF IndTypeOk
      <2>4. round[q] \in (0)..(MaxRound)
            BY SMT DEF IndTypeOk
      <2>4a. v \in ((ValidValues \union InvalidValues) \union {-1})
            BY <2>2
      <2>5. Cardinality({m \in msgs_prevote[round[q]] : m.id = v})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_prevote[round[q]] : mm.id = v} : s = m.src})
            BY <2>4, <2>4a, PrevoteValueMessagesCardinalityLeSenders
      <2>6. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote[round[q]] : mm.id = v} : s = m.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote'[round[q]] : mm.id = v} : s = m.src})
            BY <2>4, <2>4a, PrevoteSenderSetCardinalityMonotone
      <2>7. /\ Cardinality({m \in msgs_prevote[round[q]] : m.id = v}) \in Int
              /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_prevote[round[q]] : mm.id = v} : s = m.src}) \in Int
              /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_prevote'[round[q]] : mm.id = v} : s = m.src}) \in Int
              /\ ((2 * T) + 1) \in Int
            BY <2>4, <2>4a, PrevoteValueMessagesFinite, FiniteCF, FS_Union,
               FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>8. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote[round[q]] : mm.id = v} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>2, <2>5, <2>7, IntLeGeTrans1
      <2>9. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote'[round[q]] : mm.id = v} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>6, <2>7, <2>8, IntLeGeTrans1
      <2>10. {s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_prevote'[valid_round'[q]] : mm.id = valid_value'[q]} : s = m.src}
              =
              {s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_prevote'[round[q]] : mm.id = v} : s = m.src}
            BY <2>3, SMT
      <2>11. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote'[valid_round'[q]] : mm.id = valid_value'[q]} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>9, <2>10
      <2> QED BY <2>11
  <1> QED BY <1>1, <1>2

THEOREM Pres_AllIfLockedRoundThenSentCommit ==
  ASSUME TypedIndInvMin, Step PROVE AllIfLockedRoundThenSentCommit'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, locked_round'[q] # -1
               PROVE  \E rr \in (0)..(MaxRound) :
                         /\ rr <= round'[q]
                         /\ \E m \in msgs_precommit'[rr] :
                              /\ q = m.src
                              /\ m.id = locked_value'[q]
      BY DEF AllIfLockedRoundThenSentCommit
  <1>1. CASE locked_value'[q] = locked_value[q]
      <2>post. AllLockedRoundIffLockedValue'
            BY Pres_AllLockedRoundIffLockedValue
      <2>0. locked_value'[q] # -1
            BY <2>post DEF AllLockedRoundIffLockedValue
      <2>00. locked_value[q] # -1
            BY <1>1, <2>0
      <2>000. locked_round[q] # -1
            BY <2>00 DEF AllLockedRoundIffLockedValue
      <2>1. PICK rr \in (0)..(MaxRound) :
                /\ rr <= round[q]
                /\ \E m \in msgs_precommit[rr] :
                     /\ q = m.src
                     /\ m.id = locked_value[q]
            BY <2>000 DEF AllIfLockedRoundThenSentCommit
      <2>2. PICK m \in msgs_precommit[rr] :
                /\ rr <= round[q]
                /\ q = m.src
                /\ m.id = locked_value[q]
            BY <2>1
      <2>3. rr <= round[q]
            BY <2>2
      <2>4. m \in msgs_precommit'[rr]
            BY <2>2, PrecommitMonotone
      <2>5. round[q] <= round'[q]
            BY RoundMonotone DEF TypedIndInvMin, IndTypeOk
      <2>6. IndTypeOk'
            BY TypePres
      <2>7. /\ rr \in Int /\ round[q] \in Int /\ round'[q] \in Int
            BY <2>1, <2>6, ConstNat, SMT DEF TypedIndInvMin, IndTypeOk
      <2>8. rr <= round'[q]
            BY <2>3, <2>5, <2>7, SMT
      <2> QED BY <1>1, <2>1, <2>2, <2>4, <2>8
  <1>2. CASE locked_value'[q] # locked_value[q]
      <2>1. UponProposalInPrevoteOrCommitAndPrevote(q)
            BY <1>2, SMT DEF Step, InsertProposal, UponProposalInPropose,
               UponProposalInProposeAndPrevote, UponQuorumOfPrevotesAny,
               UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
               OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup, FaultyStep
      <2>2. PICK v \in ValidValues, vr \in ((0)..(MaxRound) \union {-1}) :
                /\ locked_value' = [locked_value EXCEPT ![q] = v]
                /\ locked_round' = [locked_round EXCEPT ![q] = round[q]]
                /\ msgs_precommit' =
                     [msgs_precommit EXCEPT ![round[q]] =
                       (msgs_precommit[round[q]] \union {[id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[q], src |-> q]})]
            BY <1>2, <2>1, SMT DEF UponProposalInPrevoteOrCommitAndPrevote
      <2>3. round[q] <= round'[q]
            BY RoundMonotone DEF TypedIndInvMin, IndTypeOk
      <2>4. round[q] \in (0)..(MaxRound)
            BY SMT DEF IndTypeOk
      <2>5. [id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[q], src |-> q] \in msgs_precommit'[round[q]]
            BY <2>2
      <2>6. locked_value'[q] = v
            BY <2>2, SMT DEF IndTypeOk
      <2> QED BY <2>3, <2>4, <2>5, <2>6
  <1> QED BY <1>1, <1>2

THEOREM Pres_AllLatestPrecommitHasLockedRound ==
  ASSUME TypedIndInvMin, Step PROVE AllLatestPrecommitHasLockedRound'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  \/ /\ locked_round'[q] = -1
                          /\ locked_value'[q] = -1
                          /\ \A r \in (0)..(MaxRound) : \A m \in msgs_precommit'[r] :
                               \/ q # m.src
                               \/ m.id = -1
                       \/ /\ locked_round'[q] # -1
                          /\ locked_value'[q] # -1
                          /\ \A r \in (0)..(MaxRound) : \A m \in msgs_precommit'[r] :
                               \/ \/ q # m.src
                                  \/ m.round <= locked_round'[q]
                               \/ m.id = -1
                          /\ \E m \in msgs_precommit'[locked_round'[q]] :
                               /\ q = m.src
                               /\ m.id = locked_value'[q]
      BY DEF AllLatestPrecommitHasLockedRound
  <1>1. CASE locked_round'[q] = locked_round[q] /\ locked_value'[q] = locked_value[q]
      <2>old. \/ /\ locked_round[q] = -1
                   /\ locked_value[q] = -1
                   /\ \A r \in (0)..(MaxRound) : \A m \in msgs_precommit[r] :
                        \/ q # m.src
                        \/ m.id = -1
                \/ /\ locked_round[q] # -1
                   /\ locked_value[q] # -1
                   /\ \A r \in (0)..(MaxRound) : \A m \in msgs_precommit[r] :
                        \/ \/ q # m.src
                           \/ m.round <= locked_round[q]
                        \/ m.id = -1
                   /\ \E m \in msgs_precommit[locked_round[q]] :
                        /\ q = m.src
                        /\ m.id = locked_value[q]
            BY DEF AllLatestPrecommitHasLockedRound
      <2>typep. IndTypeOk'
            BY TypePres
      <2>shape. \A r \in (0)..(MaxRound) : \A m \in msgs_precommit'[r] :
                   /\ m.round = r
                   /\ \/ m \in msgs_precommit[r]
                      \/ q # m.src
                      \/ /\ r = round[q]
                         /\ \/ m.id = -1
                            \/ /\ locked_round'[q] = round[q]
                               /\ m.id = locked_value'[q]
            BY DisjointCF, SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrevotesAny, OnQuorumOfNilPrevotes, FaultyStep, IndTypeOk
      <2>1. CASE locked_round[q] = -1
          <3>oldNil. /\ locked_value[q] = -1
                      /\ \A r \in (0)..(MaxRound) : \A m \in msgs_precommit[r] :
                           \/ q # m.src
                           \/ m.id = -1
                BY <2>old, <2>1, SMT
          <3> QED
                BY <1>1, <2>1, <3>oldNil, <2>shape, ConstNat, SMT
                DEF TypedIndInvMin, IndTypeOk
      <2>2. CASE locked_round[q] # -1
          <3>0. locked_round[q] \in (0)..(MaxRound)
                BY <2>2, SMT DEF TypedIndInvMin, IndTypeOk
          <3>oldVal. locked_value[q] # -1
                BY <2>old, <2>2, SMT
          <3>oldUni. \A r \in (0)..(MaxRound) : \A m \in msgs_precommit[r] :
                         \/ \/ q # m.src
                            \/ m.round <= locked_round[q]
                         \/ m.id = -1
                BY <2>old, <2>2, SMT
          <3>oldExist. \E m \in msgs_precommit[locked_round[q]] :
                         /\ q = m.src
                         /\ m.id = locked_value[q]
                BY <2>old, <2>2, SMT
          <3>1. PICK m \in msgs_precommit[locked_round[q]] :
                    /\ q = m.src
                    /\ m.id = locked_value[q]
                BY <3>oldExist
          <3>2. m \in msgs_precommit'[locked_round'[q]]
                BY <1>1, <2>2, <3>0, <3>1, PrecommitMonotone
          <3> QED
                BY <1>1, <2>2, <2>shape, <3>oldVal, <3>oldUni, <3>1, <3>2, SMT
      <2> QED BY <2>old, <2>1, <2>2
  <1>2. CASE locked_round'[q] # locked_round[q] \/ locked_value'[q] # locked_value[q]
      <2>1. UponProposalInPrevoteOrCommitAndPrevote(q)
            BY <1>2, SMT DEF Step, InsertProposal, UponProposalInPropose,
               UponProposalInProposeAndPrevote, UponQuorumOfPrevotesAny,
               UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
               OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup, FaultyStep
      <2>2. PICK v \in ValidValues, vr \in ((0)..(MaxRound) \union {-1}) :
                /\ locked_value' = [locked_value EXCEPT ![q] = v]
                /\ locked_round' = [locked_round EXCEPT ![q] = round[q]]
                /\ msgs_precommit' =
                     [msgs_precommit EXCEPT ![round[q]] =
                       (msgs_precommit[round[q]] \union {[id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[q], src |-> q]})]
            BY <1>2, <2>1, SMT DEF UponProposalInPrevoteOrCommitAndPrevote
      <2>3. locked_value'[q] = v /\ locked_round'[q] = round[q]
            BY <2>2, SMT DEF IndTypeOk
      <2>4. locked_round'[q] # -1 /\ locked_value'[q] # -1
            BY <2>2, <2>3, NilNotValid, SMT DEF IndTypeOk
      <2>5. [id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[q], src |-> q]
              \in msgs_precommit'[locked_round'[q]]
            BY <2>2, <2>3
      <2>6. \A r \in (0)..(MaxRound) : \A m \in msgs_precommit'[r] :
               \/ \/ q # m.src
                  \/ m.round <= locked_round'[q]
               \/ m.id = -1
            BY <2>2, <2>3, SMT DEF AllLatestPrecommitHasLockedRound,
               AllValidAndLockedRoundBounded, IndTypeOk
      <2> QED BY <2>3, <2>4, <2>5, <2>6
  <1> QED BY <1>1, <1>2

THEOREM Pres_AllIfSentPrevoteThenReceivedProposalOrTwoThirds ==
  ASSUME TypedIndInvMin, Step PROVE AllIfSentPrevoteThenReceivedProposalOrTwoThirds'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1> SUFFICES ASSUME NEW r \in (0)..(MaxRound),
                       NEW m \in msgs_prevote'[r]
               PROVE  \/ m.src \in Faulty
                      \/ m.id = -1
                      \/ /\ m.id # -1
                         /\ \/ \E prop \in msgs_propose'[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = m.id
                                  /\ prop.valid_round = -1
                            \/ \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                                  /\ \E prop \in msgs_propose'[r] :
                                       /\ prop.src = Proposer[r]
                                       /\ prop.proposal = m.id
                                       /\ rr = prop.valid_round
                                  /\ Cardinality({s \in (Corr \union Faulty) :
                                       \E pv \in {pp \in msgs_prevote'[rr] : pp.id = m.id} :
                                         s = pv.src}) >= ((2 * T) + 1)
      BY DEF AllIfSentPrevoteThenReceivedProposalOrTwoThirds
  <1>split. \/ m \in msgs_prevote[r]
             \/ m.src \in Faulty
             \/ (\E p \in Corr, v \in (ValidValues \union InvalidValues) :
                  /\ r = round[p]
                  /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> -1]
                       \in msgs_propose[round[p]]
                  /\ m = [id |-> (IF /\ v \in ValidValues
                                      /\ \/ locked_round[p] = -1
                                         \/ locked_value[p] = v
                                    THEN v ELSE -1),
                          kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p])
             \/ (\E p \in Corr, v \in (ValidValues \union InvalidValues), vr \in (0)..(MaxRound) :
                  /\ r = round[p]
                  /\ vr < round[p]
                  /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr]
                       \in msgs_propose[round[p]]
                  /\ Cardinality({pv \in msgs_prevote[vr] : v = pv.id}) >= ((2 * T) + 1)
                  /\ m = [id |-> (IF /\ v \in ValidValues
                                      /\ \/ locked_round[p] <= vr
                                         \/ locked_value[p] = v
                                    THEN v ELSE -1),
                          kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p])
             \/ (\E p \in Corr :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p])
      BY DisjointCF, SMT DEF Step, FaultyStep, UponProposalInPropose,
         UponProposalInProposeAndPrevote, OnTimeoutPropose
  <1>1. CASE m \in msgs_prevote[r]
      <2>old. \/ m.src \in Faulty
                \/ m.id = -1
                \/ /\ m.id # -1
                   /\ \/ \E prop \in msgs_propose[r] :
                            /\ prop.src = Proposer[r]
                            /\ prop.proposal = m.id
                            /\ prop.valid_round = -1
                      \/ \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                            /\ \E prop \in msgs_propose[r] :
                                 /\ prop.src = Proposer[r]
                                 /\ prop.proposal = m.id
                                 /\ rr = prop.valid_round
                            /\ Cardinality({s \in (Corr \union Faulty) :
                                 \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                                   s = pv.src}) >= ((2 * T) + 1)
            BY <1>1 DEF AllIfSentPrevoteThenReceivedProposalOrTwoThirds
      <2>f. CASE m.src \in Faulty
          <3> QED BY <2>f
      <2>nil. CASE m.id = -1
          <3> QED BY <2>nil
      <2>good. CASE /\ m.id # -1
                    /\ \/ \E prop \in msgs_propose[r] :
                             /\ prop.src = Proposer[r]
                             /\ prop.proposal = m.id
                             /\ prop.valid_round = -1
                       \/ \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                             /\ \E prop \in msgs_propose[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = m.id
                                  /\ rr = prop.valid_round
                             /\ Cardinality({s \in (Corr \union Faulty) :
                                  \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                                    s = pv.src}) >= ((2 * T) + 1)
          <3>propCase. CASE \E prop \in msgs_propose[r] :
                             /\ prop.src = Proposer[r]
                             /\ prop.proposal = m.id
                             /\ prop.valid_round = -1
              <4> PICK prop \in msgs_propose[r] :
                             /\ prop.src = Proposer[r]
                             /\ prop.proposal = m.id
                             /\ prop.valid_round = -1
                    BY <3>propCase
              <4>pnew. prop \in msgs_propose'[r]
                    BY ProposeMonotone
              <4> QED BY <2>good, <4>pnew
          <3>quorumCase. CASE \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                             /\ \E prop \in msgs_propose[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = m.id
                                  /\ rr = prop.valid_round
                             /\ Cardinality({s \in (Corr \union Faulty) :
                                  \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                                    s = pv.src}) >= ((2 * T) + 1)
              <4>oldQ. PICK rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                             /\ \E prop \in msgs_propose[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = m.id
                                  /\ rr = prop.valid_round
                             /\ Cardinality({s \in (Corr \union Faulty) :
                                  \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                                    s = pv.src}) >= ((2 * T) + 1)
                    BY <3>quorumCase
              <4>oldProp. PICK prop \in msgs_propose[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = m.id
                                  /\ rr = prop.valid_round
                    BY <4>oldQ
              <4>rty. rr \in (0)..(MaxRound)
                    BY <4>oldQ
              <4>idty. m.id \in ((ValidValues \union InvalidValues) \union {-1})
                    \* Extract the id-field type from IndTypeOk's prevote record-set typing:
                    \* SMT cannot project the field out of the set-builder monolithically.
                    <5>1. m \in {[id |-> t[3], kind |-> "PREVOTE_OF_VOTEKIND", round |-> t[2], src |-> t[1]] :
                                   t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
                          BY <1>1 DEF IndTypeOk
                    <5>2. PICK t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1})) :
                             m = [id |-> t[3], kind |-> "PREVOTE_OF_VOTEKIND", round |-> t[2], src |-> t[1]]
                          BY <5>1
                    <5>3. m.id = t[3]  BY <5>2
                    <5> QED  BY <5>2, <5>3
              <4>mono. Cardinality({s \in (Corr \union Faulty) :
                            \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                              s = pv.src})
                        <=
                        Cardinality({s \in (Corr \union Faulty) :
                            \E pv \in {pp \in msgs_prevote'[rr] : pp.id = m.id} :
                              s = pv.src})
                    BY <4>rty, <4>idty, PrevoteSenderSetCardinalityMonotone
              <4>types. /\ Cardinality({s \in (Corr \union Faulty) :
                               \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                                 s = pv.src}) \in Int
                          /\ Cardinality({s \in (Corr \union Faulty) :
                               \E pv \in {pp \in msgs_prevote'[rr] : pp.id = m.id} :
                                 s = pv.src}) \in Int
                          /\ ((2 * T) + 1) \in Int
                    BY FiniteCF, FS_Union, FS_Subset, FS_CardinalityType, ConstNat, SMT
              <4>newq. Cardinality({s \in (Corr \union Faulty) :
                            \E pv \in {pp \in msgs_prevote'[rr] : pp.id = m.id} :
                              s = pv.src}) >= ((2 * T) + 1)
                    BY <4>oldQ, <4>mono, <4>types, IntLeGeTrans1
              <4>pnew. prop \in msgs_propose'[r]
                    BY ProposeMonotone
              <4> QED BY <2>good, <4>oldQ, <4>oldProp, <4>pnew, <4>newq
          <3> QED BY <2>good, <3>propCase, <3>quorumCase
      <2> QED BY <2>old, <2>f, <2>nil, <2>good
  <1>2. CASE m.src \in Faulty
      <2> QED BY <1>2
  <1>3. CASE \E p \in Corr, v \in (ValidValues \union InvalidValues) :
                  /\ r = round[p]
                  /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> -1]
                       \in msgs_propose[round[p]]
                  /\ m = [id |-> (IF /\ v \in ValidValues
                                      /\ \/ locked_round[p] = -1
                                         \/ locked_value[p] = v
                                    THEN v ELSE -1),
                          kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]
      <2> QED BY <1>3, ProposeMonotone, SMT
  <1>4. CASE \E p \in Corr, v \in (ValidValues \union InvalidValues), vr \in (0)..(MaxRound) :
                  /\ r = round[p]
                  /\ vr < round[p]
                  /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr]
                       \in msgs_propose[round[p]]
                  /\ Cardinality({pv \in msgs_prevote[vr] : v = pv.id}) >= ((2 * T) + 1)
                  /\ m = [id |-> (IF /\ v \in ValidValues
                                      /\ \/ locked_round[p] <= vr
                                         \/ locked_value[p] = v
                                    THEN v ELSE -1),
                          kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]
      <2>wit. PICK p \in Corr, v \in (ValidValues \union InvalidValues), vr \in (0)..(MaxRound) :
                  /\ r = round[p]
                  /\ vr < round[p]
                  /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr]
                       \in msgs_propose[round[p]]
                  /\ Cardinality({pv \in msgs_prevote[vr] : v = pv.id}) >= ((2 * T) + 1)
                  /\ m = [id |-> (IF /\ v \in ValidValues
                                      /\ \/ locked_round[p] <= vr
                                         \/ locked_value[p] = v
                                    THEN v ELSE -1),
                          kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]
            BY <1>4
      <2>nil. CASE m.id = -1
          <3> QED BY <2>nil
      <2>nonnull. CASE m.id # -1
          <3>mid. m.id = v
                BY <2>wit, <2>nonnull, SMT
          <3>msgLeSenders. Cardinality({pv \in msgs_prevote[vr] : pv.id = v})
                  <=
                  Cardinality({s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote[vr] : pp.id = v} : s = pv.src})
                BY PrevoteValueMessagesCardinalityLeSenders
          <3>mono. Cardinality({s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote[vr] : pp.id = v} : s = pv.src})
                  <=
                  Cardinality({s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote'[vr] : pp.id = v} : s = pv.src})
                BY PrevoteSenderSetCardinalityMonotone
          <3>finCF. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
          <3>fin1. IsFiniteSet({pv \in msgs_prevote[vr] : pv.id = v})
                BY PrevoteValueMessagesFinite
          <3>fin2. IsFiniteSet({s \in (Corr \union Faulty) :
                     \E pv \in {pp \in msgs_prevote[vr] : pp.id = v} : s = pv.src})
                <4>sub. {s \in (Corr \union Faulty) : \E pv \in {pp \in msgs_prevote[vr] : pp.id = v} : s = pv.src}
                          \subseteq (Corr \union Faulty)  OBVIOUS
                <4> QED  BY <4>sub, <3>finCF, FS_Subset
          <3>fin3. IsFiniteSet({s \in (Corr \union Faulty) :
                     \E pv \in {pp \in msgs_prevote'[vr] : pp.id = v} : s = pv.src})
                <4>sub. {s \in (Corr \union Faulty) : \E pv \in {pp \in msgs_prevote'[vr] : pp.id = v} : s = pv.src}
                          \subseteq (Corr \union Faulty)  OBVIOUS
                <4> QED  BY <4>sub, <3>finCF, FS_Subset
          <3>types. /\ Cardinality({pv \in msgs_prevote[vr] : pv.id = v}) \in Int
                      /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in {pp \in msgs_prevote[vr] : pp.id = v} : s = pv.src}) \in Int
                      /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in {pp \in msgs_prevote'[vr] : pp.id = v} : s = pv.src}) \in Int
                      /\ ((2 * T) + 1) \in Int
                BY <3>fin1, <3>fin2, <3>fin3, FiniteCF, FS_Union, FS_Subset,
                   FS_CardinalityType, ConstNat, SMT
          <3>oldSenders. Cardinality({s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote[vr] : pp.id = v} : s = pv.src})
                  >= ((2 * T) + 1)
                BY <2>wit, <3>msgLeSenders, <3>types, IntLeGeTrans1
          <3>newSenders. Cardinality({s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote'[vr] : pp.id = v} : s = pv.src})
                  >= ((2 * T) + 1)
                BY <3>oldSenders, <3>mono, <3>types, IntLeGeTrans1
          <3>pnew. [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr]
                    \in msgs_propose'[r]
                BY <2>wit, ProposeMonotone
          <3>qpost. \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                      /\ \E prop \in msgs_propose'[r] :
                           /\ prop.src = Proposer[r]
                           /\ prop.proposal = m.id
                           /\ rr = prop.valid_round
                      /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in {pp \in msgs_prevote'[rr] : pp.id = m.id} :
                             s = pv.src}) >= ((2 * T) + 1)
              <4>rrIn. vr \in {rrr \in (0)..(MaxRound) : rrr < r}
                    BY <2>wit
              <4>propOk. /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr]
                              \in msgs_propose'[r]
                          /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr].src
                              = Proposer[r]
                          /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr].proposal
                              = m.id
                          /\ vr = [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr].valid_round
                    BY <2>wit, <3>mid, <3>pnew, SMT
              <4>card. Cardinality({s \in (Corr \union Faulty) :
                            \E pv \in {pp \in msgs_prevote'[vr] : pp.id = m.id} :
                              s = pv.src}) >= ((2 * T) + 1)
                    BY <3>mid, <3>newSenders
              <4> QED BY <4>rrIn, <4>propOk, <4>card
          <3> QED BY <2>nonnull, <3>qpost
      <2> QED BY <2>nil, <2>nonnull
  <1>5. CASE \E p \in Corr :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]
      <2> QED BY <1>5
  <1> QED BY <1>split, <1>1, <1>2, <1>3, <1>4, <1>5

THEOREM Pres_IfSentPrecommitThenSentPrevote ==
  ASSUME TypedIndInvMin, Step PROVE IfSentPrecommitThenSentPrevote'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1> SUFFICES ASSUME NEW r \in (0)..(MaxRound),
                       NEW m \in msgs_precommit'[r],
                       m.src \in Corr
               PROVE  \E pv \in msgs_prevote'[r] : pv.src = m.src
      BY DEF IfSentPrecommitThenSentPrevote
  <1>split. \/ m \in msgs_precommit[r]
             \/ \E p \in Corr :
                  /\ step[p] = "PREVOTE_OF_STEP"
                  /\ r = round[p]
                  /\ m.src = p
      BY DisjointCF, SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote,
         UponQuorumOfPrevotesAny, OnQuorumOfNilPrevotes, FaultyStep
  <1>1. CASE m \in msgs_precommit[r]
      <2>1. PICK pv \in msgs_prevote[r] : pv.src = m.src
            BY <1>1 DEF IfSentPrecommitThenSentPrevote
      <2>2. pv \in msgs_prevote'[r]
            BY <2>1, PrevoteMonotone
      <2> QED BY <2>1, <2>2
  <1>2. CASE \E p \in Corr :
                  /\ step[p] = "PREVOTE_OF_STEP"
                  /\ r = round[p]
                  /\ m.src = p
      <2> PICK p \in Corr :
                  /\ step[p] = "PREVOTE_OF_STEP"
                  /\ r = round[p]
                  /\ m.src = p
            BY <1>2
      <2>1. PICK pv \in msgs_prevote[round[p]] :
                /\ pv.id \in ((ValidValues \union InvalidValues) \union {-1})
                /\ p = pv.src
            BY DEF AllIfInPrevoteThenSentPrevote
      <2>2. pv \in msgs_prevote'[r]
            BY <2>1, PrevoteMonotone
      <2> QED BY <2>1, <2>2
  <1> QED BY <1>split, <1>1, <1>2

THEOREM Pres_IfSentPrecommitThenReceivedTwoThirds ==
  ASSUME TypedIndInvMin, Step PROVE IfSentPrecommitThenReceivedTwoThirds'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1> SUFFICES ASSUME NEW r \in (0)..(MaxRound),
                       NEW m \in msgs_precommit'[r],
                       m.src \in Corr
               PROVE  \/ /\ m.id \in ValidValues
                          /\ Cardinality({s \in (Corr \union Faulty) :
                               \E pv \in {pp \in msgs_prevote'[r] : pp.id = m.id} :
                                 s = pv.src}) >= ((2 * T) + 1)
                       \/ /\ m.id = -1
                          /\ Cardinality({s \in (Corr \union Faulty) :
                               \E pv \in msgs_prevote'[r] : s = pv.src}) >= ((2 * T) + 1)
      BY DEF IfSentPrecommitThenReceivedTwoThirds
  <1>split. \/ m \in msgs_precommit[r]
             \/ (\E p \in Corr, v \in ValidValues, vr \in ((0)..(MaxRound) \union {-1}) :
                   /\ r = round[p]
                   /\ m = [id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                   /\ Cardinality({pv \in msgs_prevote[round[p]] : v = pv.id}) >= ((2 * T) + 1))
             \/ (\E p \in Corr : \E ev \in SUBSET msgs_prevote[round[p]] :
                   /\ r = round[p]
                   /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                   /\ Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) >= ((2 * T) + 1))
             \/ (\E p \in Corr :
                   /\ r = round[p]
                   /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                   /\ Cardinality({pv \in msgs_prevote[round[p]] : pv.id = -1}) >= ((2 * T) + 1))
      \* Only 4 actions touch msgs_precommit; the other 7 keep it via UNCHANGED. Split
      \* per action so each SMT call reasons about a single action body (the monolithic
      \* call over all four bodies at once was too large to discharge).
      <2>msel. \/ msgs_precommit' = msgs_precommit
               \/ \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
               \/ \E p \in Corr : UponQuorumOfPrevotesAny(p)
               \/ \E p \in Corr : OnQuorumOfNilPrevotes(p)
               \/ FaultyStep
          BY DEF Step
      <2>1. CASE msgs_precommit' = msgs_precommit
          BY <2>1
      <2>2. CASE \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
          <3> PICK p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)  BY <2>2
          <3> QED  BY SMT DEF UponProposalInPrevoteOrCommitAndPrevote
      <2>3. CASE \E p \in Corr : UponQuorumOfPrevotesAny(p)
          <3> PICK p \in Corr : UponQuorumOfPrevotesAny(p)  BY <2>3
          \* msgs_precommit' has a fixed shape independent of the evidence witness, so
          \* extract it without instantiating the existential; keep the prevote quorum
          \* (whose set-builder has a nested \E) as a separate existential fact.
          <3>mp. msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                   (msgs_precommit[round[p]] \union {[id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND",
                                                     round |-> round[p], src |-> p]})]
              BY DEF UponQuorumOfPrevotesAny
          <3>ev. \E ev \in SUBSET msgs_prevote[round[p]] :
                   Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) >= ((2 * T) + 1)
              BY Zenon DEF UponQuorumOfPrevotesAny
          <3>1. CASE m \in msgs_precommit[r]  BY <3>1
          <3>2. CASE m \notin msgs_precommit[r]
              <4>eq. r = round[p] /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  BY <3>mp, <3>2, SMT
              <4>d3. \E pp \in Corr : \E ev \in SUBSET msgs_prevote[round[pp]] :
                       /\ r = round[pp]
                       /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[pp], src |-> pp]
                       /\ Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) >= ((2 * T) + 1)
                  BY <3>ev, <4>eq
              <4> QED  BY <4>d3
          <3> QED  BY <3>1, <3>2
      <2>4. CASE \E p \in Corr : OnQuorumOfNilPrevotes(p)
          <3> PICK p \in Corr : OnQuorumOfNilPrevotes(p)  BY <2>4
          <3>a. /\ Cardinality({pv \in msgs_prevote[round[p]] : pv.id = -1}) >= ((2 * T) + 1)
                /\ msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                     (msgs_precommit[round[p]] \union {[id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND",
                                                       round |-> round[p], src |-> p]})]
              BY DEF OnQuorumOfNilPrevotes
          <3>1. CASE m \in msgs_precommit[r]  BY <3>1
          <3>2. CASE m \notin msgs_precommit[r]
              <4>eq. r = round[p] /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  BY <3>a, <3>2, SMT
              <4>d4. \E pp \in Corr :
                       /\ r = round[pp]
                       /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[pp], src |-> pp]
                       /\ Cardinality({pv \in msgs_prevote[round[pp]] : pv.id = -1}) >= ((2 * T) + 1)
                  BY <3>a, <4>eq
              <4> QED  BY <4>d4
          <3> QED  BY <3>1, <3>2
      <2>5. CASE FaultyStep
          BY <2>5, DisjointCF, SMT DEF FaultyStep
      <2> QED  BY <2>msel, <2>1, <2>2, <2>3, <2>4, <2>5
  <1>1. CASE m \in msgs_precommit[r]
      <2>old. \/ /\ m.id \in ValidValues
                   /\ Cardinality({s \in (Corr \union Faulty) :
                        \E pv \in {pp \in msgs_prevote[r] : pp.id = m.id} :
                          s = pv.src}) >= ((2 * T) + 1)
                \/ /\ m.id = -1
                   /\ Cardinality({s \in (Corr \union Faulty) :
                        \E pv \in msgs_prevote[r] : s = pv.src}) >= ((2 * T) + 1)
            BY <1>1 DEF IfSentPrecommitThenReceivedTwoThirds
      <2>vcase. CASE /\ m.id \in ValidValues
                    /\ Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in {pp \in msgs_prevote[r] : pp.id = m.id} :
                           s = pv.src}) >= ((2 * T) + 1)
          <3>idtype. m.id \in ((ValidValues \union InvalidValues) \union {-1})
                BY <2>vcase
          <3>mono. Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in {pp \in msgs_prevote[r] : pp.id = m.id} :
                           s = pv.src})
                    <=
                    Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in {pp \in msgs_prevote'[r] : pp.id = m.id} :
                           s = pv.src})
                BY <3>idtype, PrevoteSenderSetCardinalityMonotone
          <3>types. /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in {pp \in msgs_prevote[r] : pp.id = m.id} :
                             s = pv.src}) \in Int
                       /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in {pp \in msgs_prevote'[r] : pp.id = m.id} :
                             s = pv.src}) \in Int
                       /\ ((2 * T) + 1) \in Int
                BY FiniteCF, FS_Union, FS_Subset, FS_CardinalityType, ConstNat, SMT
          <3>post. Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in {pp \in msgs_prevote'[r] : pp.id = m.id} :
                           s = pv.src}) >= ((2 * T) + 1)
                BY <2>vcase, <3>mono, <3>types, IntLeGeTrans1
          <3> QED BY <2>vcase, <3>post
      <2>nilcase. CASE /\ m.id = -1
                      /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in msgs_prevote[r] : s = pv.src}) >= ((2 * T) + 1)
          <3>mono. Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in msgs_prevote[r] : s = pv.src})
                    <=
                    Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in msgs_prevote'[r] : s = pv.src})
                BY PrevoteAllSenderSetCardinalityMonotone
          <3>types. /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in msgs_prevote[r] : s = pv.src}) \in Int
                       /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in msgs_prevote'[r] : s = pv.src}) \in Int
                       /\ ((2 * T) + 1) \in Int
                BY FiniteCF, FS_Union, FS_Subset, FS_CardinalityType, ConstNat, SMT
          <3>post. Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in msgs_prevote'[r] : s = pv.src}) >= ((2 * T) + 1)
                BY <2>nilcase, <3>mono, <3>types, IntLeGeTrans1
          <3> QED BY <2>nilcase, <3>post
      <2> QED BY <2>old, <2>vcase, <2>nilcase
  <1>2. CASE \E p \in Corr, v \in ValidValues, vr \in ((0)..(MaxRound) \union {-1}) :
                  /\ r = round[p]
                  /\ m = [id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({pv \in msgs_prevote[round[p]] : v = pv.id}) >= ((2 * T) + 1)
      <2>wit. PICK p \in Corr, v \in ValidValues, vr \in ((0)..(MaxRound) \union {-1}) :
                  /\ r = round[p]
                  /\ m = [id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({pv \in msgs_prevote[round[p]] : v = pv.id}) >= ((2 * T) + 1)
            BY <1>2
      <2>rid. r = round[p]
            BY <2>wit
      <2>mid. m.id = v
            BY <2>wit
      <2>rty. round[p] \in (0)..(MaxRound)
            BY SMT DEF IndTypeOk
      <2>vty. v \in ((ValidValues \union InvalidValues) \union {-1})
            BY <2>wit
      <2>eq. {pv \in msgs_prevote[round[p]] : pv.id = v}
              =
              {pv \in msgs_prevote[round[p]] : v = pv.id}
            BY SMT
      <2>lb. Cardinality({pv \in msgs_prevote[round[p]] : pv.id = v}) >= ((2 * T) + 1)
            BY <2>wit, <2>eq
      <2>msgLeSenders. Cardinality({pv \in msgs_prevote[round[p]] : pv.id = v})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                \E pv \in {pp \in msgs_prevote[round[p]] : pp.id = v} : s = pv.src})
            BY <2>rty, <2>vty, PrevoteValueMessagesCardinalityLeSenders
      <2>mono. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in {pp \in msgs_prevote[round[p]] : pp.id = v} : s = pv.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in {pp \in msgs_prevote'[round[p]] : pp.id = v} : s = pv.src})
            BY <2>rty, <2>vty, PrevoteSenderSetCardinalityMonotone
      <2>types. /\ Cardinality({pv \in msgs_prevote[round[p]] : pv.id = v}) \in Int
                  /\ Cardinality({s \in (Corr \union Faulty) :
                       \E pv \in {pp \in msgs_prevote[round[p]] : pp.id = v} : s = pv.src}) \in Int
                  /\ Cardinality({s \in (Corr \union Faulty) :
                       \E pv \in {pp \in msgs_prevote'[round[p]] : pp.id = v} : s = pv.src}) \in Int
                  /\ ((2 * T) + 1) \in Int
            BY <2>rty, <2>vty, PrevoteValueMessagesFinite, FiniteCF, FS_Union,
               FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>oldSenders. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in {pp \in msgs_prevote[round[p]] : pp.id = v} : s = pv.src})
              >= ((2 * T) + 1)
            BY <2>lb, <2>msgLeSenders, <2>types, IntLeGeTrans1
      <2>newSenders. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in {pp \in msgs_prevote'[round[p]] : pp.id = v} : s = pv.src})
              >= ((2 * T) + 1)
            BY <2>oldSenders, <2>mono, <2>types, IntLeGeTrans1
      <2>posteq. {s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote'[r] : pp.id = m.id} : s = pv.src}
                  =
                  {s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote'[round[p]] : pp.id = v} : s = pv.src}
            BY <2>rid, <2>mid, SMT
      <2> QED BY <2>mid, <2>newSenders, <2>posteq
  <1>3. CASE \E p \in Corr : \E ev \in SUBSET msgs_prevote[round[p]] :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) >= ((2 * T) + 1)
      <2>wit. PICK p \in Corr : \E ev \in SUBSET msgs_prevote[round[p]] :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) >= ((2 * T) + 1)
            BY <1>3
      <2>wit2. PICK ev \in SUBSET msgs_prevote[round[p]] :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) >= ((2 * T) + 1)
            BY <2>wit
      <2>rty. round[p] \in (0)..(MaxRound)
            BY SMT DEF IndTypeOk
      <2>evLeAll. Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                \E pv \in msgs_prevote[round[p]] : s = pv.src})
            BY <2>rty, PrevoteEvidenceSenderSetCardinalityLeAllSenders
      <2>mono. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote[round[p]] : s = pv.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote'[round[p]] : s = pv.src})
            BY <2>rty, PrevoteAllSenderSetCardinalityMonotone
      <2>types. /\ Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) \in Int
                  /\ Cardinality({s \in (Corr \union Faulty) :
                       \E pv \in msgs_prevote[round[p]] : s = pv.src}) \in Int
                  /\ Cardinality({s \in (Corr \union Faulty) :
                       \E pv \in msgs_prevote'[round[p]] : s = pv.src}) \in Int
                  /\ ((2 * T) + 1) \in Int
            BY FiniteCF, FS_Union, FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>oldAll. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote[round[p]] : s = pv.src})
              >= ((2 * T) + 1)
            BY <2>wit2, <2>evLeAll, <2>types, IntLeGeTrans1
      <2>newAll. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote'[round[p]] : s = pv.src})
              >= ((2 * T) + 1)
            BY <2>oldAll, <2>mono, <2>types, IntLeGeTrans1
      <2>posteq. {s \in (Corr \union Faulty) : \E pv \in msgs_prevote'[r] : s = pv.src}
                  =
                  {s \in (Corr \union Faulty) : \E pv \in msgs_prevote'[round[p]] : s = pv.src}
            BY <2>wit2, SMT
      <2> QED BY <2>wit2, <2>newAll, <2>posteq
  <1>4. CASE \E p \in Corr :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({pv \in msgs_prevote[round[p]] : pv.id = -1}) >= ((2 * T) + 1)
      <2>wit. PICK p \in Corr :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({pv \in msgs_prevote[round[p]] : pv.id = -1}) >= ((2 * T) + 1)
            BY <1>4
      <2>rty. round[p] \in (0)..(MaxRound)
            BY SMT DEF IndTypeOk
      <2>nilty. -1 \in ((ValidValues \union InvalidValues) \union {-1})
            BY SMT
      <2>msgLeAll. Cardinality({pv \in msgs_prevote[round[p]] : pv.id = -1})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                \E pv \in msgs_prevote[round[p]] : s = pv.src})
            BY <2>rty, <2>nilty, PrevoteValueMessagesCardinalityLeAllSenders
      <2>mono. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote[round[p]] : s = pv.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote'[round[p]] : s = pv.src})
            BY <2>rty, PrevoteAllSenderSetCardinalityMonotone
      <2>types. /\ Cardinality({pv \in msgs_prevote[round[p]] : pv.id = -1}) \in Int
                  /\ Cardinality({s \in (Corr \union Faulty) :
                       \E pv \in msgs_prevote[round[p]] : s = pv.src}) \in Int
                  /\ Cardinality({s \in (Corr \union Faulty) :
                       \E pv \in msgs_prevote'[round[p]] : s = pv.src}) \in Int
                  /\ ((2 * T) + 1) \in Int
            BY <2>rty, <2>nilty, PrevoteValueMessagesFinite, FiniteCF, FS_Union,
               FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>oldAll. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote[round[p]] : s = pv.src})
              >= ((2 * T) + 1)
            BY <2>wit, <2>msgLeAll, <2>types, IntLeGeTrans1
      <2>newAll. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote'[round[p]] : s = pv.src})
              >= ((2 * T) + 1)
            BY <2>oldAll, <2>mono, <2>types, IntLeGeTrans1
      <2>posteq. {s \in (Corr \union Faulty) : \E pv \in msgs_prevote'[r] : s = pv.src}
                  =
                  {s \in (Corr \union Faulty) : \E pv \in msgs_prevote'[round[p]] : s = pv.src}
            BY <2>wit, SMT
      <2> QED BY <2>wit, <2>newAll, <2>posteq
  <1> QED BY <1>split, <1>1, <1>2, <1>3, <1>4

THEOREM Pres_AllNoEquivocationByCorrect ==
  ASSUME TypedIndInvMin, Step PROVE AllNoEquivocationByCorrect'
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1> SUFFICES ASSUME NEW r \in (0)..(MaxRound)
               PROVE  /\ \E pv \in ValidValues :
                           \E pvr \in ((0)..(MaxRound) \union {-1}) :
                             \A mp \in msgs_propose'[r] :
                               \/ mp.src \in Faulty
                               \/ /\ /\ mp.src = Proposer[r]
                                     /\ pv = mp.proposal
                                  /\ pvr = mp.valid_round
                      /\ \A q \in Corr :
                           \E vv \in (ValidValues \union {-1}) :
                             \A mv \in msgs_prevote'[r] :
                               q = mv.src => vv = mv.id
                      /\ \A q \in Corr :
                           \E cv \in (ValidValues \union {-1}) :
                             \A mc \in msgs_precommit'[r] :
                               q = mc.src => cv = mc.id
      BY DEF AllNoEquivocationByCorrect
  <1>prop. \E pv \in ValidValues :
               \E pvr \in ((0)..(MaxRound) \union {-1}) :
                 \A mp \in msgs_propose'[r] :
                   \/ mp.src \in Faulty
                   \/ /\ /\ mp.src = Proposer[r]
                         /\ pv = mp.proposal
                      /\ pvr = mp.valid_round
      <2>old. PICK oldv \in ValidValues, oldvr \in ((0)..(MaxRound) \union {-1}) :
                    \A mp \in msgs_propose[r] :
                      \/ mp.src \in Faulty
                      \/ /\ /\ mp.src = Proposer[r]
                            /\ oldv = mp.proposal
                         /\ oldvr = mp.valid_round
            BY DEF AllNoEquivocationByCorrect
      <2>sel. \/ msgs_propose' = msgs_propose
               \/ FaultyStep
               \/ \E p \in Corr : InsertProposal(p)
            BY DEF Step
      <2>same. CASE msgs_propose' = msgs_propose
          <3> QED BY <2>same, <2>old
      <2>faulty. CASE FaultyStep
          <3> QED BY <2>faulty, <2>old, DisjointCF, SMT DEF FaultyStep
      <2>insert. CASE \E p \in Corr : InsertProposal(p)
          <3> PICK p \in Corr : InsertProposal(p) BY <2>insert
          <3> PICK v \in ValidValues :
                msgs_propose' = [msgs_propose EXCEPT ![round[p]] =
                  (msgs_propose[round[p]] \union {[proposal |-> (IF valid_value[p] # -1 THEN valid_value[p] ELSE v),
                     round |-> round[p], src |-> p, valid_round |-> valid_round[p]]})]
              BY <2>insert DEF InsertProposal
          <3>pty. /\ p = Proposer[round[p]]
                  /\ \A mp \in msgs_propose[round[p]] : p # mp.src
                  /\ valid_value[p] \in (ValidValues \union {-1})
                  /\ valid_round[p] \in ((0)..(MaxRound) \union {-1})
                BY <2>insert DEF InsertProposal, IndTypeOk
          <3>newVal. (IF valid_value[p] # -1 THEN valid_value[p] ELSE v) \in ValidValues
                BY <3>pty, NilNotValid, SMT
          <3>1. CASE r = round[p]
              <4>oldFaulty. \A mp \in msgs_propose[r] : mp.src \in Faulty
                    BY <2>old, <3>pty, <3>1, SMT
              <4> QED BY <3>1, <3>pty, <3>newVal, <4>oldFaulty, SMT
          <3>2. CASE r # round[p]
              <4> QED BY <2>old, <3>2, SMT
          <3> QED BY <3>1, <3>2
      <2> QED BY <2>sel, <2>same, <2>faulty, <2>insert
  <1>prevote. \A q \in Corr :
                 \E vv \in (ValidValues \union {-1}) :
                   \A mv \in msgs_prevote'[r] :
                     q = mv.src => vv = mv.id
      <2> SUFFICES ASSUME NEW q \in Corr
                   PROVE  \E vv \in (ValidValues \union {-1}) :
                            \A mv \in msgs_prevote'[r] :
                              q = mv.src => vv = mv.id
          OBVIOUS
      <2>old. PICK oldv \in (ValidValues \union {-1}) :
                    \A mv \in msgs_prevote[r] : q = mv.src => oldv = mv.id
            BY DEF AllNoEquivocationByCorrect
      <2>sel. \/ msgs_prevote' = msgs_prevote
               \/ FaultyStep
               \/ \E p \in Corr : UponProposalInPropose(p)
               \/ \E p \in Corr : UponProposalInProposeAndPrevote(p)
               \/ \E p \in Corr : OnTimeoutPropose(p)
            BY DEF Step
      <2>same. CASE msgs_prevote' = msgs_prevote
          <3> QED BY <2>same, <2>old
      <2>faulty. CASE FaultyStep
          <3> QED BY <2>faulty, <2>old, DisjointCF, SMT DEF FaultyStep
      <2>corr. ASSUME NEW p \in Corr,
                       NEW idv \in (ValidValues \union {-1}),
                       step[p] = "PROPOSE_OF_STEP",
                       msgs_prevote' =
                         [msgs_prevote EXCEPT ![round[p]] =
                           (msgs_prevote[round[p]] \union {[id |-> idv,
                             kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                PROVE  \E vv \in (ValidValues \union {-1}) :
                         \A mv \in msgs_prevote'[r] :
                           q = mv.src => vv = mv.id
          <3>1. CASE q = p /\ r = round[p]
              <4>none. \A mv \in msgs_prevote[r] : q # mv.src
                    BY <2>corr, <3>1 DEF AllNoFutureMessagesSent
              <4> QED BY <2>corr, <3>1, <4>none, SMT
          <3>2. CASE ~(q = p /\ r = round[p])
              <4> QED BY <2>corr, <2>old, <3>2, SMT
          <3> QED BY <3>1, <3>2
      <2>proposal. CASE \E p \in Corr : UponProposalInPropose(p)
          <3> PICK p \in Corr : UponProposalInPropose(p) BY <2>proposal
          <3>wit. \E idv \in (ValidValues \union {-1}) :
                    /\ step[p] = "PROPOSE_OF_STEP"
                    /\ msgs_prevote' =
                         [msgs_prevote EXCEPT ![round[p]] =
                           (msgs_prevote[round[p]] \union {[id |-> idv,
                             kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                BY <2>proposal, SMT DEF UponProposalInPropose
          <3> QED BY <3>wit, <2>corr
      <2>proposalPrevote. CASE \E p \in Corr : UponProposalInProposeAndPrevote(p)
          <3> PICK p \in Corr : UponProposalInProposeAndPrevote(p) BY <2>proposalPrevote
          <3>wit. \E idv \in (ValidValues \union {-1}) :
                    /\ step[p] = "PROPOSE_OF_STEP"
                    /\ msgs_prevote' =
                         [msgs_prevote EXCEPT ![round[p]] =
                           (msgs_prevote[round[p]] \union {[id |-> idv,
                             kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                BY <2>proposalPrevote, SMT DEF UponProposalInProposeAndPrevote
          <3> QED BY <3>wit, <2>corr
      <2>timeout. CASE \E p \in Corr : OnTimeoutPropose(p)
          <3> PICK p \in Corr : OnTimeoutPropose(p) BY <2>timeout
          <3>wit. /\ step[p] = "PROPOSE_OF_STEP"
                  /\ msgs_prevote' =
                       [msgs_prevote EXCEPT ![round[p]] =
                         (msgs_prevote[round[p]] \union {[id |-> -1,
                           kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                BY <2>timeout DEF OnTimeoutPropose
          <3>nil. -1 \in (ValidValues \union {-1}) BY SMT
          <3> QED BY <3>wit, <3>nil, <2>corr
      <2> QED BY <2>sel, <2>same, <2>faulty, <2>proposal, <2>proposalPrevote,
         <2>timeout
  <1>precommit. \A q \in Corr :
                   \E cv \in (ValidValues \union {-1}) :
                     \A mc \in msgs_precommit'[r] :
                       q = mc.src => cv = mc.id
      <2> SUFFICES ASSUME NEW q \in Corr
                   PROVE  \E cv \in (ValidValues \union {-1}) :
                            \A mc \in msgs_precommit'[r] :
                              q = mc.src => cv = mc.id
          OBVIOUS
      <2>old. PICK oldv \in (ValidValues \union {-1}) :
                    \A mc \in msgs_precommit[r] : q = mc.src => oldv = mc.id
            BY DEF AllNoEquivocationByCorrect
      <2>sel. \/ msgs_precommit' = msgs_precommit
               \/ FaultyStep
               \/ \E p \in Corr : UponQuorumOfPrevotesAny(p)
               \/ \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
               \/ \E p \in Corr : OnQuorumOfNilPrevotes(p)
            BY DEF Step
      <2>same. CASE msgs_precommit' = msgs_precommit
          <3> QED BY <2>same, <2>old
      <2>faulty. CASE FaultyStep
          <3> QED BY <2>faulty, <2>old, DisjointCF, SMT DEF FaultyStep
      <2>corr. ASSUME NEW p \in Corr,
                       NEW idv \in (ValidValues \union {-1}),
                       step[p] = "PREVOTE_OF_STEP",
                       msgs_precommit' =
                         [msgs_precommit EXCEPT ![round[p]] =
                           (msgs_precommit[round[p]] \union {[id |-> idv,
                             kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                PROVE  \E cv \in (ValidValues \union {-1}) :
                         \A mc \in msgs_precommit'[r] :
                           q = mc.src => cv = mc.id
          <3>1. CASE q = p /\ r = round[p]
              <4>none. \A mc \in msgs_precommit[r] : q # mc.src
                    BY <2>corr, <3>1 DEF AllNoFutureMessagesSent
              <4> QED BY <2>corr, <3>1, <4>none, SMT
          <3>2. CASE ~(q = p /\ r = round[p])
              <4> QED BY <2>corr, <2>old, <3>2, SMT
          <3> QED BY <3>1, <3>2
      <2>quorumPrevotes. CASE \E p \in Corr : UponQuorumOfPrevotesAny(p)
          <3> PICK p \in Corr : UponQuorumOfPrevotesAny(p) BY <2>quorumPrevotes
          <3>wit. /\ step[p] = "PREVOTE_OF_STEP"
                  /\ msgs_precommit' =
                       [msgs_precommit EXCEPT ![round[p]] =
                         (msgs_precommit[round[p]] \union {[id |-> -1,
                           kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                BY <2>quorumPrevotes DEF UponQuorumOfPrevotesAny
          <3>nil. -1 \in (ValidValues \union {-1}) BY SMT
          <3> QED BY <3>wit, <3>nil, <2>corr
      <2>proposalPrevoteCommit. CASE \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
          <3> PICK p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p) BY <2>proposalPrevoteCommit
          <3>wit. \/ msgs_precommit' = msgs_precommit
                  \/ \E idv \in ValidValues :
                       /\ step[p] = "PREVOTE_OF_STEP"
                       /\ msgs_precommit' =
                            [msgs_precommit EXCEPT ![round[p]] =
                              (msgs_precommit[round[p]] \union {[id |-> idv,
                                kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                BY <2>proposalPrevoteCommit, SMT DEF UponProposalInPrevoteOrCommitAndPrevote
          <3>same. CASE msgs_precommit' = msgs_precommit
              <4> QED BY <3>same, <2>old
          <3>send. CASE \E idv \in ValidValues :
                       /\ step[p] = "PREVOTE_OF_STEP"
                       /\ msgs_precommit' =
                            [msgs_precommit EXCEPT ![round[p]] =
                              (msgs_precommit[round[p]] \union {[id |-> idv,
                                kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              <4> PICK idv \in ValidValues :
                       /\ step[p] = "PREVOTE_OF_STEP"
                       /\ msgs_precommit' =
                            [msgs_precommit EXCEPT ![round[p]] =
                              (msgs_precommit[round[p]] \union {[id |-> idv,
                                kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                    BY <3>send
              <4>idty. idv \in (ValidValues \union {-1}) OBVIOUS
              <4> QED BY <3>send, <4>idty, <2>corr
          <3> QED BY <3>wit, <3>same, <3>send
      <2>nilPrevotes. CASE \E p \in Corr : OnQuorumOfNilPrevotes(p)
          <3> PICK p \in Corr : OnQuorumOfNilPrevotes(p) BY <2>nilPrevotes
          <3>wit. /\ step[p] = "PREVOTE_OF_STEP"
                  /\ msgs_precommit' =
                       [msgs_precommit EXCEPT ![round[p]] =
                         (msgs_precommit[round[p]] \union {[id |-> -1,
                           kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                BY <2>nilPrevotes DEF OnQuorumOfNilPrevotes
          <3>nil. -1 \in (ValidValues \union {-1}) BY SMT
          <3> QED BY <3>wit, <3>nil, <2>corr
      <2> QED BY <2>sel, <2>same, <2>faulty, <2>quorumPrevotes,
         <2>proposalPrevoteCommit, <2>nilPrevotes
  <1> QED BY <1>prop, <1>prevote, <1>precommit

\* PrecommitsLockValue is NOT inductive relative to IndInvMin alone (Apalache CE): a
\* fresh prevote for w2 in a round above an existing precommit lock for w must be
\* blocked, which needs the per-process lock PrecommitLocksLaterPrevotes (and the
\* valid-round conjuncts). Hence this preservation is stated over the full TypedIndInv.
\* Proof strategy (to mechanize). Assume, for a counterexample, a post-state precommit
\* quorum for w at r0 (>= 2T+1) and a post-state prevote quorum for w2 (in ValidValues,
\* w2 # w) at some r > r0. A single correct Step changes at most one of msgs_precommit /
\* msgs_prevote (no correct action touches both; only FaultyStep does, and it adds only
\* faulty senders, which cannot supply the >= T+1 correct part of a 2T+1 quorum). So one
\* of the two quorums is entirely pre-state.
\*   - If the precommit quorum is pre-state: PrecommitsLockValue (pre) already forbids a
\*     pre-state prevote quorum for w2 in r > r0; the fresh prevote adds one correct
\*     sender (PrevoteSenderSetCardinalityMonotone), so the pre-state prevote count was
\*     exactly 2T. The >= T+1 correct precommitters of w at r0 and the >= T+1 correct
\*     prevoters of w2 at r intersect (N = 3T+1); the shared correct process c either
\*     (a) prevoted w2 at r in the pre-state -- then PrecommitLocksLaterPrevotes gives a
\*     2T+1 prevote quorum for w2 at some r1 in [r0, r), contradicting PrecommitsLockValue
\*     (pre) [r1 = r0 handled by same-round quorum uniqueness + AllNoEquivocationByCorrect];
\*     or (b) c is the acting process casting the fresh prevote -- then its prevote-guard
\*     (locked on w via AllIfLockedRoundThenSentCommit) forces a valid-round vr in [r0, r)
\*     with a 2T+1 prevote quorum for w2 (AllIfValidRoundThenTwoThirdsPrevotes /
\*     AllCorrectProposalValidRoundBelowRound), again contradicting PrecommitsLockValue.
\*   - If the precommit quorum is fresh: symmetric, the acting process precommits w at r0
\*     and the pre-state carries a prevote quorum for w2 at r.
\* This is the core research obligation; it needs PrecommitLocksLaterPrevotes and the
\* valid-round conjuncts, hence the hypothesis is the full TypedIndInv.
\*
\* NOTE: this build's backends will not match the goal PrecommitsLockValue' (a doubly-
\* quantified disjunction whose atoms are Cardinality of nested set-builders) against an
\* explicit primed unfolding, so even the SUFFICES reduction to the counterexample form
\* does not go through yet -- resolving that plumbing is a prerequisite to mechanizing
\* the argument above.
THEOREM Pres_PrecommitsLockValue ==
  ASSUME TypedIndInv, Step PROVE PrecommitsLockValue'
  <1> USE DEF TypedIndInv, IndTypeOk
  \* Reduce the primed goal to its explicit unfolded form via an equivalence step; the
  \* backends match the doubly-quantified Cardinality-disjunction goal only through this
  \* detour, not by unfolding it in place inside a SUFFICES.
  <1>unfold. PrecommitsLockValue' <=>
               (\A v_v708 \in (0)..(MaxRound), v_v709 \in ValidValues:
                  \/ (Cardinality({v_v711 \in (Corr \union Faulty): (\E v_v712 \in {v_v710 \in msgs_precommit'[v_v708]: (v_v710.id = v_v709)}: (v_v711 = v_v712.src))}) < ((2 * T) + 1))
                  \/ (\A v_v714 \in {v_v713 \in (0)..(MaxRound): (v_v713 > v_v708)}: \A v_v715 \in (ValidValues \ {v_v709}): (Cardinality({v_v717 \in (Corr \union Faulty): (\E v_v718 \in {v_v716 \in msgs_prevote'[v_v714]: (v_v716.id = v_v715)}: (v_v717 = v_v718.src))}) < ((2 * T) + 1))))
      BY DEF PrecommitsLockValue
  <1> SUFFICES \A v_v708 \in (0)..(MaxRound), v_v709 \in ValidValues:
                  \/ (Cardinality({v_v711 \in (Corr \union Faulty): (\E v_v712 \in {v_v710 \in msgs_precommit'[v_v708]: (v_v710.id = v_v709)}: (v_v711 = v_v712.src))}) < ((2 * T) + 1))
                  \/ (\A v_v714 \in {v_v713 \in (0)..(MaxRound): (v_v713 > v_v708)}: \A v_v715 \in (ValidValues \ {v_v709}): (Cardinality({v_v717 \in (Corr \union Faulty): (\E v_v718 \in {v_v716 \in msgs_prevote'[v_v714]: (v_v716.id = v_v715)}: (v_v717 = v_v718.src))}) < ((2 * T) + 1)))
      BY <1>unfold
  <1> TAKE r0 \in (0)..(MaxRound), w \in ValidValues
  \* Counterexample form: a post-state precommit quorum for w at r0 forces every other
  \* valid value w2 to lack a post-state prevote quorum in each later round r.
  <1> SUFFICES ASSUME ~(Cardinality({v_v711 \in (Corr \union Faulty): (\E v_v712 \in {v_v710 \in msgs_precommit'[r0]: (v_v710.id = w)}: (v_v711 = v_v712.src))}) < ((2 * T) + 1)),
                      NEW r \in {v_v713 \in (0)..(MaxRound): (v_v713 > r0)},
                      NEW w2 \in (ValidValues \ {w})
               PROVE  Cardinality({v_v717 \in (Corr \union Faulty): (\E v_v718 \in {v_v716 \in msgs_prevote'[r]: (v_v716.id = w2)}: (v_v717 = v_v718.src))}) < ((2 * T) + 1)
      OBVIOUS
  \* Pre-state lock (PrecommitsLockValue at (r0, w)): either w has no pre-state precommit
  \* quorum at r0, or no other valid value has a pre-state prevote quorum above r0.
  <1>pre. \/ Cardinality({s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_precommit[r0] : mm.id = w} : s = m.src}) < 2 * T + 1
          \/ (\A rr \in {x \in (0)..(MaxRound) : x > r0} : \A ww \in (ValidValues \ {w}) :
                Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote[rr] : mm.id = ww} : s = m.src}) < 2 * T + 1)
      BY Zenon, SMT DEF TypedIndInv, IndInv, PrecommitsLockValue
  \* ---- remaining mathematical core (OMITTED) --------------------------------------
  \* A single correct Step changes at most one of msgs_precommit / msgs_prevote (only
  \* FaultyStep touches both, and it adds only faulty senders, which cannot form the
  \* >= T+1 correct part of a 2T+1 quorum). So one of the two quorums is entirely
  \* pre-state. Using PrevoteSenderSetCardinalityMonotone / PrecommitSenderSetCardinality-
  \* Monotone, the fresh vote adds one correct sender, so the pre-state count was exactly
  \* 2T. The >= T+1 correct precommitters of w at r0 and the >= T+1 correct prevoters of
  \* w2 at r intersect (N = 3T+1); the shared correct process c either (a) prevoted w2 at
  \* r pre-state -> PrecommitLocksLaterPrevotes gives a 2T+1 prevote quorum for w2 at some
  \* r1 in [r0, r), contradicting <1>pre [r1 = r0: same-round quorum uniqueness +
  \* AllNoEquivocationByCorrect]; or (b) c is the acting process, whose prevote guard
  \* (locked on w) forces a valid_round vr in [r0, r) with a 2T+1 prevote quorum for w2
  \* (AllIfValidRoundThenTwoThirdsPrevotes / AllCorrectProposalValidRoundBelowRound),
  \* again contradicting <1>pre.
  <1> QED
    OMITTED

\* ---------------------------------------------------------------------------
\* TOP-LEVEL INDUCTIVE STEP: assemble type preservation + all 17 conjuncts.
\* ---------------------------------------------------------------------------
\* Preserving the 17 IndInvMin conjuncts. PrecommitsLockValue needs the extra IndInv
\* conjuncts (via Pres_PrecommitsLockValue), so the hypothesis is the full TypedIndInv;
\* the other 16 preservations only use the TypedIndInvMin part. Extending the conclusion
\* to the full TypedIndInv' requires preserving the remaining 7 support conjuncts.
THEOREM Inductive ==
  ASSUME TypedIndInv, Step
  PROVE  TypedIndInvMin'
  BY TypePres,
     Pres_AllNoFutureMessagesSent,
     Pres_AllIfInPrevoteThenSentPrevote,
     Pres_AllIfInPrecommitThenSentPrecommit,
     Pres_AllIfInDecidedThenReceivedProposal,
     Pres_AllIfInDecidedThenReceivedTwoThirds,
     Pres_AllIfInDecidedThenValidDecision,
     Pres_AllLockedRoundIffLockedValue,
     Pres_AllValidRoundIffValidValue,
     Pres_AllValidAndLockedRoundBounded,
     Pres_AllIfValidRoundThenTwoThirdsPrevotes,
     Pres_AllIfLockedRoundThenSentCommit,
     Pres_AllLatestPrecommitHasLockedRound,
     Pres_AllIfSentPrevoteThenReceivedProposalOrTwoThirds,
     Pres_IfSentPrecommitThenSentPrevote,
     Pres_IfSentPrecommitThenReceivedTwoThirds,
     Pres_AllNoEquivocationByCorrect,
     Pres_PrecommitsLockValue
  DEF TypedIndInvMin, IndInvMin, TypedIndInv, IndInv

\*****************************************************************************
\* SECTION D -- AGREEMENT
\*
\* TODO: port the Ben-Or Section D chain:
\*   quorum-uniqueness within a round  ->  cross-round strict-quorum lock
\*   (PrecommitsLockValue)  ->  decided value is backed by a 2T+1 precommit
\*   quorum (AllIfInDecidedThenReceivedTwoThirds)  ->  case-split on the two
\*   decided rounds, closing the induction with NatInductionTrusted and
\*   QuorumsIntersectInCorrect.
\* Named AgreementThm (not Agreement, which is a spec operator).
\*****************************************************************************

\* Correct/faulty senders of a precommit (resp. prevote) for value d in round r.
PCSet(r, d) == {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_precommit[r] : mm.id = d} : s = m.src}
PVSet(r, d) == {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_prevote[r] : mm.id = d} : s = m.src}

LEMMA PCSetSubset == ASSUME NEW r, NEW d PROVE PCSet(r, d) \in SUBSET (Corr \union Faulty)  BY DEF PCSet
LEMMA PVSetSubset == ASSUME NEW r, NEW d PROVE PVSet(r, d) \in SUBSET (Corr \union Faulty)  BY DEF PVSet

\* Orientation bridge: the spec writes the value test as `d = mm.id` in some
\* conjuncts and `mm.id = d` in others; both name the same set.
LEMMA PCSetFlip ==
  ASSUME NEW r, NEW d
  PROVE  PCSet(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_precommit[r] : d = mm.id} : s = m.src}
  BY DEF PCSet
LEMMA PVSetFlip ==
  ASSUME NEW r, NEW d
  PROVE  PVSet(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_prevote[r] : d = mm.id} : s = m.src}
  BY DEF PVSet

\* Cross-round lock: an earlier 2T+1 precommit quorum for va forces any later
\* 2T+1 precommit quorum's value vb to equal va.
\* Any subset of the (finite) replica set is finite.
LEMMA SubsetCFFinite == ASSUME NEW A, A \subseteq (Corr \union Faulty) PROVE IsFiniteSet(A)
  BY FiniteCF, FS_Union, FS_Subset

\* Cardinality congruence, grounded in FS_Subset (this tlapm build's backends do not
\* apply Leibniz under Cardinality on these set-builders without finiteness).
LEMMA CardCong ==
  ASSUME NEW S1, NEW S2, IsFiniteSet(S1), S1 = S2
  PROVE  Cardinality(S1) = Cardinality(S2)
  <1>1. S1 \subseteq S2 /\ S2 \subseteq S1  OBVIOUS
  <1>2. IsFiniteSet(S2)  OBVIOUS
  <1> QED  BY <1>1, <1>2, FS_Subset

LEMMA LockLemma ==
  ASSUME TypedIndInvMin,
         NEW ra \in (0)..(MaxRound), NEW rb \in (0)..(MaxRound),
         NEW va \in ValidValues, NEW vb \in ValidValues, ra < rb,
         Cardinality(PCSet(ra, va)) >= 2 * T + 1,
         Cardinality(PCSet(rb, vb)) >= 2 * T + 1
  PROVE  va = vb
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1>Ssub. PCSet(rb, vb) \in SUBSET (Corr \union Faulty)  BY PCSetSubset
  <1>corr. \E c \in Corr : c \in PCSet(rb, vb)  BY <1>Ssub, QuorumHasCorrect
  <1> PICK c \in Corr : c \in PCSet(rb, vb)  BY <1>corr
  <1> PICK mc \in msgs_precommit[rb] : mc.id = vb /\ mc.src = c  BY DEF PCSet
  <1>mcC. mc.src \in Corr /\ mc.id \in ValidValues  BY NilNotValid
  <1>mcvb. mc.id = vb  OBVIOUS
  \* A correct precommit for mc.id at rb yields a 2T+1 prevote quorum for mc.id
  \* (IfSentPrecommit; the nil-value disjunct is ruled out because mc.id is valid).
  \* Everything below works through mc.id, so no value is ever substituted inside a
  \* Cardinality — the spec's set-builder orientation now matches PVSet/PCSet directly.
  <1>pv. Cardinality(PVSet(rb, mc.id)) >= 2 * T + 1
      BY <1>mcC, NilNotValid, Zenon, SMT DEF IfSentPrecommitThenReceivedTwoThirds, PVSet
  \* PrecommitsLockValue at (ra, va): the 2T+1 precommit quorum for va blocks a
  \* 2T+1 prevote quorum for any other valid value in later rounds.
  <1>raw. \/ Cardinality(PCSet(ra, va)) < 2 * T + 1
          \/ (\A r3 \in {rr \in (0)..(MaxRound) : rr > ra} : \A v3 \in (ValidValues \ {va}) :
                Cardinality(PVSet(r3, v3)) < 2 * T + 1)
      BY Zenon, SMT DEF PrecommitsLockValue, PCSet, PVSet
  <1>finU2. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
  <1>cardNat. Cardinality(PCSet(ra, va)) \in Nat /\ Cardinality(PVSet(rb, mc.id)) \in Nat
      <2>1. PCSet(ra, va) \subseteq (Corr \union Faulty) /\ PVSet(rb, mc.id) \subseteq (Corr \union Faulty)
            BY PCSetSubset, PVSetSubset
      <2>2. IsFiniteSet(PCSet(ra, va)) /\ IsFiniteSet(PVSet(rb, mc.id))
            BY <2>1, <1>finU2, FS_Subset
      <2> QED  BY <2>2, FS_CardinalityType
  \* first disjunct of raw is false because the ASSUME gives Cardinality(PCSet(ra,va)) >= 2T+1
  <1>notD1. ~(Cardinality(PCSet(ra, va)) < 2 * T + 1)
      BY <1>cardNat, ConstNat, SMT
  <1>notlock. \A r3 \in {rr \in (0)..(MaxRound) : rr > ra} : \A v3 \in (ValidValues \ {va}) :
                Cardinality(PVSet(r3, v3)) < 2 * T + 1
      BY <1>raw, <1>notD1
  <1>inst. rb \in {rr \in (0)..(MaxRound) : rr > ra}  BY SMT
  <1> QED
      <2>1. mc.id \notin (ValidValues \ {va})
          <3> SUFFICES ASSUME mc.id \in (ValidValues \ {va}) PROVE FALSE  OBVIOUS
          <3>1. Cardinality(PVSet(rb, mc.id)) < 2 * T + 1  BY <1>notlock, <1>inst
          <3> QED  BY <3>1, <1>pv, <1>cardNat, ConstNat, SMT
      <2> QED  BY <2>1, <1>mcC, <1>mcvb

THEOREM AgreementThm ==
  TypedIndInvMin => Agreement
  <1> SUFFICES ASSUME TypedIndInvMin, NEW p1 \in Corr, NEW p2 \in Corr,
                      decision[p1] # -1, decision[p2] # -1
               PROVE  decision[p1] = decision[p2]
      BY DEF Agreement
  <1> USE DEF TypedIndInvMin, IndInvMin, IndTypeOk
  <1>d1v. decision[p1] \in ValidValues  BY NilNotValid
  <1>d2v. decision[p2] \in ValidValues  BY NilNotValid
  <1>s1. step[p1] = "DECIDED_OF_STEP"  BY <1>d1v DEF AllIfInDecidedThenValidDecision
  <1>s2. step[p2] = "DECIDED_OF_STEP"  BY <1>d2v DEF AllIfInDecidedThenValidDecision
  <1>q1. \E r \in (0)..(MaxRound) : Cardinality(PCSet(r, decision[p1])) >= 2 * T + 1
      BY <1>s1, Zenon, SMT DEF AllIfInDecidedThenReceivedTwoThirds, PCSet
  <1>q2. \E r \in (0)..(MaxRound) : Cardinality(PCSet(r, decision[p2])) >= 2 * T + 1
      BY <1>s2, Zenon, SMT DEF AllIfInDecidedThenReceivedTwoThirds, PCSet
  <1> PICK r1 \in (0)..(MaxRound) : Cardinality(PCSet(r1, decision[p1])) >= 2 * T + 1  BY <1>q1
  <1> PICK r2 \in (0)..(MaxRound) : Cardinality(PCSet(r2, decision[p2])) >= 2 * T + 1  BY <1>q2
  <1>caseEQ. CASE r1 = r2
      <2>sub1. PCSet(r1, decision[p1]) \in SUBSET (Corr \union Faulty)  BY PCSetSubset
      <2>sub2. PCSet(r1, decision[p2]) \in SUBSET (Corr \union Faulty)  BY PCSetSubset
      <2>ca2. Cardinality(PCSet(r1, decision[p2])) >= 2 * T + 1  BY <1>caseEQ
      <2>corr. \E c \in Corr : c \in PCSet(r1, decision[p1]) /\ c \in PCSet(r1, decision[p2])
          BY <2>sub1, <2>sub2, <2>ca2, QuorumsIntersectInCorrect
      <2> PICK c \in Corr : c \in PCSet(r1, decision[p1]) /\ c \in PCSet(r1, decision[p2])  BY <2>corr
      <2>c1. \E m \in msgs_precommit[r1] : m.id = decision[p1] /\ m.src = c  BY DEF PCSet
      <2>c2. \E m \in msgs_precommit[r1] : m.id = decision[p2] /\ m.src = c  BY DEF PCSet
      <2> QED  BY <2>c1, <2>c2 DEF AllNoEquivocationByCorrect
  <1>caseNE. CASE r1 # r2
      <2>0. r1 \in (0)..(MaxRound) /\ r2 \in (0)..(MaxRound) /\ r1 # r2  BY <1>caseNE
      <2>1. r1 < r2 \/ r2 < r1  BY <2>0, ConstNat, SMT
      <2>2. CASE r1 < r2  BY <2>2, <1>d1v, <1>d2v, LockLemma
      <2>3. CASE r2 < r1  BY <2>3, <1>d1v, <1>d2v, LockLemma
      <2> QED  BY <2>1, <2>2, <2>3
  <1> QED  BY <1>caseEQ, <1>caseNE

=============================================================================
