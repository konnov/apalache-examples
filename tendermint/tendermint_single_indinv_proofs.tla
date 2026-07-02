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
 * Current status: BOOTSTRAP. The A/B/C/D skeleton is in place. One conjunct,
 * `AllValidAndLockedRoundBounded`, is fully decomposed across all Step actions
 * and proved end-to-end to lock in the per-action `Pres_*` pattern. All other
 * obligations (Section A quorum lemmas, base case, type preservation, the other
 * 16 inductive-step conjuncts, and Section D agreement) are OMITTED stubs to be
 * filled in incrementally.
 *
 * Environment: tlapm (TLAPS) build `b064bce-dirty` (`tlapm --version`), using the
 * stdlib TLAPS + FiniteSetTheorems modules (no Isabelle backend; all obligations
 * discharged by Zenon/SMT). The spec `EXTENDS Apalache`; the community
 * `Apalache.tla` crashes this tlapm build (its `RECURSIVE ApaFoldSet` with a
 * higher-order operator argument trips the frontend), so a minimal parse-time
 * shim `Apalache.tla` sits in this directory (see its header). Verify with:
 *   tlapm --stretch 2 --threads 4 -I . tendermint_single_indinv_proofs.tla
 *   => "All 71 obligations proved" (the AllValidAndLockedRoundBounded family and
 *      the assemblers); every OMITTED stub contributes no obligation, exit 0.
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

\* Base case of induction. TODO: SUFFICES ASSUME Init; USE DEF Init; the message
\* logs start empty and per-process fields start at nil/0, so each IndInvMin
\* conjunct holds trivially (most \A over empty message sets, the round/value
\* flags all -1 or 0).
THEOREM InitInd ==
  Init => TypedIndInvMin
OMITTED

\* Type preservation. TODO: one case per Step action showing IndTypeOk'.
THEOREM TypePres ==
  ASSUME TypedIndInvMin, Step
  PROVE  IndTypeOk'
OMITTED

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
        OBVIOUS
  <1>5. valid_round[q] <= round[q] /\ locked_round[q] <= round[q]
        OBVIOUS
  <1> QED
      BY <1>1, <1>2, <1>3, <1>4, <1>5

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
        OBVIOUS
  <1>3. /\ DOMAIN round = Corr
        /\ round[p] \in Int /\ round[q] \in Int
        OBVIOUS
  <1>4. valid_round[q] <= round[q] /\ locked_round[q] <= round[q]
        OBVIOUS
  <1> QED
      BY <1>1, <1>2, <1>3, <1>4

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
        OBVIOUS
  <1>3. /\ DOMAIN round = Corr
        /\ round[p] \in Int /\ round[q] \in Int
        OBVIOUS
  <1>4. valid_round[q] <= round[q] /\ locked_round[q] <= round[q]
        OBVIOUS
  <1> QED
      BY <1>1, <1>2, <1>3, <1>4

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
OMITTED

THEOREM Pres_AllIfInPrecommitThenSentPrecommit ==
  ASSUME TypedIndInvMin, Step PROVE AllIfInPrecommitThenSentPrecommit'
OMITTED

THEOREM Pres_AllIfInDecidedThenReceivedProposal ==
  ASSUME TypedIndInvMin, Step PROVE AllIfInDecidedThenReceivedProposal'
OMITTED

THEOREM Pres_AllIfInDecidedThenReceivedTwoThirds ==
  ASSUME TypedIndInvMin, Step PROVE AllIfInDecidedThenReceivedTwoThirds'
OMITTED

THEOREM Pres_AllIfInDecidedThenValidDecision ==
  ASSUME TypedIndInvMin, Step PROVE AllIfInDecidedThenValidDecision'
OMITTED

THEOREM Pres_AllLockedRoundIffLockedValue ==
  ASSUME TypedIndInvMin, Step PROVE AllLockedRoundIffLockedValue'
OMITTED

THEOREM Pres_AllValidRoundIffValidValue ==
  ASSUME TypedIndInvMin, Step PROVE AllValidRoundIffValidValue'
OMITTED

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
