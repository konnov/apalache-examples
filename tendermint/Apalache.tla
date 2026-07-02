--------------------------- MODULE Apalache -----------------------------------
(*
 * Minimal parse-time shim for TLAPS, providing only the Apalache operators that
 * `tendermint_single_indinv.tla` references. The full community Apalache.tla
 * defines ApaFoldSet with `RECURSIVE ApaFoldSet(_,_,_)` and a higher-order
 * operator argument, which crashes this tlapm build's dependency analysis
 * (Failure "use instead the class E_visit.iter_concrete"). We only need the
 * module to *parse*: the two conjuncts that use ApaFoldSet live in the full
 * IndInv / IndInit, NOT in the targeted TypedIndInvMin, so no TLAPS obligation
 * ever unfolds ApaFoldSet.
 *
 * !! This is an opaque stub with UNSOUND semantics for ApaFoldSet. Before
 *    proving the two full-IndInv fold conjuncts (AllRoundsBelowHavePrecommit-
 *    Quorum, AllValidInCurrentRoundPrecommitted), replace this with a real fold
 *    theory (e.g. community FiniteSetsExt!FoldSet + its theorems).
 *)
EXTENDS Integers, Sequences, FiniteSets

\* Opaque stub. Real semantics: left fold of __Op over __S starting from __v.
ApaFoldSet(__Op(_,_), __v, __S) == __v

===============================================================================
