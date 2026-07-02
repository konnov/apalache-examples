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
OMITTED

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
OMITTED

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
OMITTED

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
OMITTED

THEOREM Pres_AllIfLockedRoundThenSentCommit ==
  ASSUME TypedIndInvMin, Step PROVE AllIfLockedRoundThenSentCommit'
OMITTED

THEOREM Pres_AllLatestPrecommitHasLockedRound ==
  ASSUME TypedIndInvMin, Step PROVE AllLatestPrecommitHasLockedRound'
OMITTED

THEOREM Pres_AllIfSentPrevoteThenReceivedProposalOrTwoThirds ==
  ASSUME TypedIndInvMin, Step PROVE AllIfSentPrevoteThenReceivedProposalOrTwoThirds'
OMITTED

THEOREM Pres_IfSentPrecommitThenSentPrevote ==
  ASSUME TypedIndInvMin, Step PROVE IfSentPrecommitThenSentPrevote'
OMITTED

THEOREM Pres_IfSentPrecommitThenReceivedTwoThirds ==
  ASSUME TypedIndInvMin, Step PROVE IfSentPrecommitThenReceivedTwoThirds'
OMITTED

THEOREM Pres_AllNoEquivocationByCorrect ==
  ASSUME TypedIndInvMin, Step PROVE AllNoEquivocationByCorrect'
OMITTED

THEOREM Pres_PrecommitsLockValue ==
  ASSUME TypedIndInvMin, Step PROVE PrecommitsLockValue'
OMITTED

\* ---------------------------------------------------------------------------
\* TOP-LEVEL INDUCTIVE STEP: assemble type preservation + all 17 conjuncts.
\* ---------------------------------------------------------------------------
THEOREM Inductive ==
  ASSUME TypedIndInvMin, Step
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
  DEF TypedIndInvMin, IndInvMin

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

THEOREM AgreementThm ==
  TypedIndInvMin => Agreement
OMITTED

=============================================================================
