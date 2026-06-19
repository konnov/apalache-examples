-------------------------- MODULE Ben_or83_proofs --------------------------
(*
 * TLAPS proofs for the Ben-Or '83 inductive invariant.
 *
 * Goals:
 *   1. `IndInv` is inductive: base case `Init => IndInv` (Section B) and the
 *      step `IndInv /\ [Next]_vars => IndInv'` (Section C).
 *   2. `IndInv => AgreementInv` (Section D).
 *
 * Status: STRUCTURE MACHINE-CHECKED. `tlapm` proves all 310 non-omitted obligations
 * (the full decomposition: base case, type preservation, the [Next]_vars case algebra
 * for all 13 preservation lemmas, every frame case, and the Section D agreement
 * skeleton incl. the NaturalsInduction wiring). What remains are `OMITTED` admits,
 * each tagged `TODO`, for the genuinely hard leaves: the quorum/cardinality arguments
 * (a value gaining/keeping a quorum) and the LockLemma inductive step. Fill them in
 * priority order (see Ben_or83_inductive.tla header and the project plan).
 *
 * Two `OMITTED` leaves are NOT mathematical TODOs but caveats:
 *   - InitInd L5/L12: FALSE at round 0 under ROUNDS = Nat (algorithm numbers rounds
 *     from 1); use ROUNDS == Nat \ {0} for a fully-closed base case.
 *   - Pres_L6_F: trivially true (FaultyStep does not touch value/decision) but blocked
 *     by a tlapm backend crash on FaultyStep's two-variable set-map.
 *
 * Checked with: tlapm (TLAPS) + stdlib FiniteSetTheorems, NaturalsInduction, TLAPS,
 * and the community `Variants` module on the search path:
 *   tlapm --toolbox 0 0 Ben_or83_proofs.tla
 *
 * Igor Konnov & Claude, June 2026
 *)
EXTENDS Ben_or83_inductive, FiniteSetTheorems, NaturalsInduction, TLAPS

\*****************************************************************************
\* NAMED ASSUMPTIONS
\*
\* The module-level ASSUME in Ben_or83.tla is anonymous; we restate the parts
\* we cite here under names, and surface facts the lemmas rely on implicitly.
\*****************************************************************************

\* The protocol assumption, named so proofs can USE it.
ASSUME NTF == N > 5 * T /\ Cardinality(CORRECT) = N - F /\ Cardinality(FAULTY) = F

\* A Cardinality-free handle on the resilience bound. Abstract arithmetic lemmas must
\* cite THIS, not NTF: any `Cardinality(...)` term in the hypotheses derails the SMT
\* backend's integer reasoning (see the Arith_* lemmas below).
ASSUME NgtT == N > 5 * T

\* Implicit in the spec (ALL == CORRECT \cup FAULTY with Cardinality(ALL) = N
\* requires disjointness). TODO: confirm with the spec author that this is intended.
ASSUME DisjointCF == CORRECT \cap FAULTY = {}

\* Cardinality is only meaningful for finite sets; the model has finitely many replicas.
ASSUME FiniteCF == IsFiniteSet(CORRECT) /\ IsFiniteSet(FAULTY)

\* The actual number of faults is bounded by T and non-negative (confirmed by author).
ASSUME FleqT == 0 <= F /\ F <= T /\ 0 <= T

\* The protocol parameters are natural numbers (counts of replicas).
ASSUME ConstNat == N \in Nat /\ T \in Nat /\ F \in Nat

\* ROUNDS is the set of positive natural rounds. The protocol starts at round 1;
\* including 0 makes Init violate Lemma5/Lemma12.
ASSUME RoundsNat == ROUNDS = Nat \ {0}

THEOREM RoundPos ==
  ASSUME NEW r \in ROUNDS
  PROVE  r \in Nat /\ r >= 1
  BY RoundsNat

LEMMA Arith_PosNotLtOne ==
  ASSUME NEW r \in Nat, r >= 1
  PROVE  ~(r < 1)
  BY ConstNat

LEMMA RoundPredInRounds ==
  ASSUME NEW r \in ROUNDS, r # 1
  PROVE  r - 1 \in ROUNDS
  BY RoundsNat, ConstNat

\*****************************************************************************
\* VARIANTS AXIOMS
\*
\* TLAPS has no built-in theory for Variant/VariantTag/VariantGetUnsafe. The
\* facts below are provable from the community `Variants` module; we state them
\* as axioms here to keep the skeleton self-contained.
\* TODO: replace by USE of the Variants module's own theorems once on the path.
\*****************************************************************************

ASSUME VariantAx ==
  /\ \A s, r, v :
        /\ IsD2(D2(s, r, v))
        /\ ~ IsQ2(D2(s, r, v))
        /\ AsD2(D2(s, r, v)) = [ src |-> s, r |-> r, v |-> v ]
  /\ \A s, r :
        /\ IsQ2(Q2(s, r))
        /\ ~ IsD2(Q2(s, r))
        /\ AsQ2(Q2(s, r)) = [ src |-> s, r |-> r ]
  \* every type-2 message is exactly one of D2/Q2
  /\ \A m : IsD2(m) <=> ~ IsQ2(m)
  \* round-trip: a D2 message is reconstructed from its fields
  /\ \A m : IsD2(m) => m = D2(AsD2(m).src, AsD2(m).r, AsD2(m).v)

\*****************************************************************************
\* SECTION A -- FOUNDATIONAL CARDINALITY / QUORUM LEMMAS
\*****************************************************************************

\* The replica universe is finite with cardinality N.
THEOREM ALL_Card == IsFiniteSet(ALL) /\ Cardinality(ALL) = N
  <1>1. IsFiniteSet(ALL)
        BY FiniteCF, FS_Union DEF ALL
  <1>2. Cardinality(CORRECT \cap FAULTY) = 0
        BY DisjointCF, FS_EmptySet
  <1>3. Cardinality(ALL) = Cardinality(CORRECT) + Cardinality(FAULTY)
        BY FiniteCF, FS_Union, FS_CardinalityType, <1>2 DEF ALL
  <1> QED
        BY <1>1, <1>3, NTF, ConstNat

\* Senders sets are subsets of ALL (the spec filters ALL on purpose), hence finite.
THEOREM Senders1_Sub ==
  ASSUME NEW S
  PROVE  Senders1(S) \subseteq ALL /\ IsFiniteSet(Senders1(S))
        /\ Cardinality(Senders1(S)) <= N
  <1>1. Senders1(S) \subseteq ALL
        BY DEF Senders1
  <1> QED
        BY <1>1, ALL_Card, FS_Subset

THEOREM Senders1_Mono ==
  ASSUME NEW A, NEW B, A \subseteq B
  PROVE  Cardinality(Senders1(A)) <= Cardinality(Senders1(B))
  <1>sub. Senders1(A) \subseteq Senders1(B) BY DEF Senders1
  <1>fin. IsFiniteSet(Senders1(B)) BY Senders1_Sub
  <1> QED BY <1>sub, <1>fin, FS_Subset

THEOREM Senders2_Sub ==
  ASSUME NEW S
  PROVE  Senders2(S) \subseteq ALL /\ IsFiniteSet(Senders2(S))
        /\ Cardinality(Senders2(S)) <= N
  <1>1. Senders2(S) \subseteq ALL
        BY DEF Senders2
  <1> QED
        BY <1>1, ALL_Card, FS_Subset

THEOREM Senders2_Mono ==
  ASSUME NEW A, NEW B, A \subseteq B
  PROVE  Cardinality(Senders2(A)) <= Cardinality(Senders2(B))
  <1>sub. Senders2(A) \subseteq Senders2(B) BY DEF Senders2
  <1>fin. IsFiniteSet(Senders2(B)) BY Senders2_Sub
  <1> QED BY <1>sub, <1>fin, FS_Subset

\* Any subset of ALL is finite with cardinality at most N.
THEOREM SubAll_Finite ==
  ASSUME NEW Q, Q \subseteq ALL
  PROVE  IsFiniteSet(Q) /\ Cardinality(Q) <= N
  BY ALL_Card, FS_Subset

\* ABSTRACT ARITHMETIC LEMMAS (Paxos style).
\* These are stated over plain Nat variables and proved by SMT. We apply them by
\* instantiating the Nat variables with `Cardinality(...)` terms. This indirection is
\* essential: when a `Cardinality(...)` term appears directly in an obligation's
\* hypotheses, the SMT backend fails even trivial integer reasoning -- but a lemma
\* APPLICATION only matches hypotheses, so the arithmetic stays Cardinality-free.

\* A set of >= N - 2*T elements cannot consist solely of <= F faulty ones (N > 5*T, F <= T).
LEMMA Arith_NotAllFaulty ==
  ASSUME NEW a \in Nat, a >= N - 2 * T, a <= F
  PROVE  FALSE
  BY NgtT, FleqT, ConstNat

\* A set of >= T+1 elements cannot consist solely of <= F faulty ones (F <= T).
LEMMA Arith_TplusOneNotFaulty ==
  ASSUME NEW a \in Nat, a >= T + 1, a <= F
  PROVE  FALSE
  BY FleqT, ConstNat

LEMMA Arith_GeTrans ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a >= c, a <= b
  PROVE  b >= c
  BY ConstNat

LEMMA Arith_DoubleGtMono ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, 2 * a > c, a <= b
  PROVE  2 * b > c
  BY ConstNat

\* CORE QUORUM INTERSECTION: two quorums of >= N - T senders intersect, and the
\* intersection necessarily contains a correct replica (since N > 5*T).
THEOREM QuorumIntersect ==
  ASSUME NEW QA, NEW QB,
         QA \subseteq ALL, QB \subseteq ALL,
         Cardinality(QA) >= N - T, Cardinality(QB) >= N - T
  PROVE  /\ Cardinality(QA \cap QB) >= N - 2 * T
         /\ \E id \in QA \cap QB : id \in CORRECT
  <1>1. IsFiniteSet(QA) /\ IsFiniteSet(QB) /\ IsFiniteSet(QA \cup QB)
              /\ IsFiniteSet(QA \cap QB)
        BY SubAll_Finite, FS_Union, FS_Intersection
  <1>2. Cardinality(QA \cup QB) <= N
        BY SubAll_Finite
  <1>3. Cardinality(QA \cup QB) = Cardinality(QA) + Cardinality(QB)
                                    - Cardinality(QA \cap QB)
        BY <1>1, FS_Union
  <1>4. Cardinality(QA \cap QB) >= N - 2 * T
        BY <1>1, <1>2, <1>3, FS_CardinalityType, NTF, FleqT, ConstNat
  <1>5. (QA \cap QB) \ CORRECT \subseteq FAULTY
        BY DEF ALL
  <1>6. Cardinality((QA \cap QB) \ CORRECT) <= F
        BY <1>5, FiniteCF, FS_Subset, NTF
  \* If the intersection had no correct replica it would be all faulty, so its
  \* cardinality would be <= F < N - 2*T, contradicting <1>4.
  <1>7. \E id \in QA \cap QB : id \in CORRECT
        \* If no member were correct, QA \cap QB would be all faulty, so its cardinality
        \* would be <= F; but it is >= N - 2*T > F (from N > 5*T, F <= T) -- contradiction.
        <2>1. SUFFICES ASSUME \A id \in QA \cap QB : id \notin CORRECT
                       PROVE  FALSE
              OBVIOUS
        <2>2. QA \cap QB = (QA \cap QB) \ CORRECT
              BY <2>1
        <2>3. Cardinality(QA \cap QB) <= F
              BY <2>2, <1>6
        <2>4. Cardinality(QA \cap QB) \in Nat
              BY <1>1, FS_CardinalityType
        <2> QED
              BY Arith_NotAllFaulty, <1>4, <2>3, <2>4
  <1> QED
        BY <1>4, <1>7

\* MAJORITY INTERSECTION: two > (N+T)/2 quorums of senders meet in a correct replica.
\* (The type-1 quorums backing a D2 message exceed half, not N-T.) The cardinality
\* arithmetic with `2 * Cardinality(...)` premises poisons SMT, so we PICK plain Nats
\* equal to each cardinality and do the arithmetic on those.
THEOREM MajCardBound ==
  ASSUME NEW QA, NEW QB, QA \subseteq ALL, QB \subseteq ALL,
         2 * Cardinality(QA) > N + T, 2 * Cardinality(QB) > N + T
  PROVE  Cardinality(QA \cap QB) >= T + 1
  <1>1. IsFiniteSet(QA) /\ IsFiniteSet(QB) /\ IsFiniteSet(QA \cup QB)
              /\ IsFiniteSet(QA \cap QB)
        BY SubAll_Finite, FS_Union, FS_Intersection
  <1>2. Cardinality(QA \cup QB) <= N BY SubAll_Finite
  <1>3. Cardinality(QA \cup QB) = Cardinality(QA) + Cardinality(QB) - Cardinality(QA \cap QB)
        BY <1>1, FS_Union
  <1>card. Cardinality(QA) \in Nat /\ Cardinality(QB) \in Nat
           /\ Cardinality(QA \cup QB) \in Nat /\ Cardinality(QA \cap QB) \in Nat
        BY <1>1, FS_CardinalityType
  <1>pa. PICK ca \in Nat : ca = Cardinality(QA) BY <1>card
  <1>pb. PICK cb \in Nat : cb = Cardinality(QB) BY <1>card
  <1>pu. PICK cu \in Nat : cu = Cardinality(QA \cup QB) BY <1>card
  <1>pi. PICK ci \in Nat : ci = Cardinality(QA \cap QB) BY <1>card
  <1>e1. 2 * ca > N + T BY <1>pa
  <1>e2. 2 * cb > N + T BY <1>pb
  <1>e3. cu <= N BY <1>pu, <1>2
  <1>e4. cu = ca + cb - ci BY <1>pa, <1>pb, <1>pu, <1>pi, <1>3
  <1>s1. ca + cb > N + T BY <1>e1, <1>e2, ConstNat
  <1>s2. ci > T BY <1>s1, <1>e3, <1>e4, ConstNat
  <1> QED BY <1>s2, <1>pi, ConstNat

THEOREM MajorityIntersect ==
  ASSUME NEW QA, NEW QB, QA \subseteq ALL, QB \subseteq ALL,
         2 * Cardinality(QA) > N + T, 2 * Cardinality(QB) > N + T
  PROVE  \E id \in QA \cap QB : id \in CORRECT
  <1>1. IsFiniteSet(QA \cap QB) BY SubAll_Finite, FS_Intersection
  <1>card. Cardinality(QA \cap QB) \in Nat BY <1>1, FS_CardinalityType
  <1>4. Cardinality(QA \cap QB) >= T + 1 BY MajCardBound
  <1>5. (QA \cap QB) \ CORRECT \subseteq FAULTY BY DEF ALL
  <1>6. Cardinality((QA \cap QB) \ CORRECT) <= F BY <1>5, FiniteCF, FS_Subset, NTF
  <1>7. \E id \in QA \cap QB : id \in CORRECT
        <2>1. SUFFICES ASSUME \A id \in QA \cap QB : id \notin CORRECT PROVE FALSE OBVIOUS
        <2>2. QA \cap QB = (QA \cap QB) \ CORRECT BY <2>1
        <2>3. Cardinality(QA \cap QB) <= F BY <2>2, <1>6
        <2> QED BY Arith_TplusOneNotFaulty, <1>4, <2>3, <1>card
  <1> QED BY <1>7

\* A correct replica that sent value v contributes a correct sender; faulty
\* senders number at most F. Used to turn ">half senders" into ">half correct".
THEOREM FaultyBound ==
  ASSUME NEW S, S \subseteq ALL
  PROVE  Cardinality(S \cap FAULTY) <= F
  BY FiniteCF, FS_Subset, NTF

\*****************************************************************************
\* MESSAGE-COUNTING (sender bound).
\* The D2 messages of one round/value with a faulty sender number at most F,
\* because m |-> AsD2(m).src injects them into FAULTY. Reusable for the quorum
\* lemmas. The map is an injection thanks to the Variant round-trip (VariantAx):
\* for m in msgs2[r] with the round constrained to r, m = D2(src, r, v).
\* (Workaround note: FS_Image crashes this tlapm build on SetOfAll, so we use the
\* first-order FS_Injection with an explicit injection function.)
\*****************************************************************************

\* The D2 messages for round r and value v sent by faulty replicas.
FaultyD2(r, v) ==
  { m \in msgs2[r] : IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in FAULTY }

\* The injection FaultyD2(r,v) -> FAULTY mapping a message to its sender.
FaultyD2Fn(r, v) == [ m \in FaultyD2(r, v) |-> AsD2(m).src ]

\* The injection is injective: two faulty D2(r,v) messages with the same sender are
\* equal (round-trip reconstructs each as D2(src, r, v)). Top-level so Zenon discharges
\* the beta-reduction + reconstruction in one shot (nested steps fail in this build).
THEOREM FaultyD2Injective ==
  ASSUME NEW r, NEW v,
         \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r,
         NEW a \in FaultyD2(r, v), NEW b \in FaultyD2(r, v),
         FaultyD2Fn(r, v)[a] = FaultyD2Fn(r, v)[b]
  PROVE  a = b
  BY Zenon, VariantAx DEF FaultyD2, FaultyD2Fn

\* Hence at most F faulty D2(r,v) messages.
THEOREM FaultyD2Bound ==
  ASSUME NEW r, NEW v,
         \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r
  PROVE  Cardinality(FaultyD2(r, v)) <= F
  <1>1. FaultyD2Fn(r, v) \in [ FaultyD2(r, v) -> FAULTY ]
        BY DEF FaultyD2, FaultyD2Fn
  <1>2. \A a, b \in FaultyD2(r, v) :
            FaultyD2Fn(r, v)[a] = FaultyD2Fn(r, v)[b] => a = b
        BY FaultyD2Injective
  <1>3. FaultyD2Fn(r, v) \in Injection(FaultyD2(r, v), FAULTY)
        BY <1>1, <1>2 DEF Injection, IsInjective
  <1>4. Cardinality(FaultyD2(r, v)) <= Cardinality(FAULTY)
        BY <1>3, FiniteCF, FS_Injection
  <1> QED
        BY <1>4, NTF

\*****************************************************************************
\* MESSAGE-SHAPE.  To apply FaultyD2Bound one needs the round invariant
\*   TypeOK => for m \in msgs2[r] with IsD2(m), AsD2(m).r = r
\* (so that messages of msgs2[r] are exactly D2(src, r, v)).
\*
\* The challenge: PICK-ing the TypeOK witnesses dumps a giant
\*   msgs2 = [r |-> {SetOfAll} \cup {SetOfAll}]
\* equation into context, and a `msgs2[rr]` term in the hypotheses poisons theorem
\* application (like a Cardinality term does). HIDE crashes this tlapm build. The
\* working pattern: derive a SMALL existential about msgs2[rr] with the heavy PICK kept
\* LOCAL to its sub-proof, then hand it to ShapeFromExists which abstracts msgs2[rr]
\* into a fresh variable `mset` and rewrites the goal via SUFFICES (no msgs2[rr] term in
\* the hard reasoning).
\*****************************************************************************

\* The D2 / Q2 parts of msgs2[rr] given the TypeOK witnesses A1D, A1Q.
DPof(A1D, rr) == { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
QPof(A1Q, rr) == { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } }

\* A message in the D2/Q2 decomposition that is a D2 lands in the D2 part with round rr.
THEOREM ShapeHelper ==
  ASSUME NEW rr, NEW A1D, NEW A1Q, NEW m,
         m \in DPof(A1D, rr) \union QPof(A1Q, rr), IsD2(m)
  PROVE  AsD2(m).r = rr
  <1>1. m \notin QPof(A1Q, rr)
        <2> SUFFICES ASSUME m \in QPof(A1Q, rr) PROVE FALSE OBVIOUS
        <2>1. PICK mq \in { m \in A1Q: m.r = rr } : m = Q2(mq.src, rr) BY DEF QPof
        <2> QED BY <2>1, VariantAx
  <1>2. PICK md \in { m \in A1D: m.r = rr } : m = D2(md.src, rr, md.v)
        BY <1>1 DEF DPof
  <1> QED BY <1>2, VariantAx

\* The raw TypeOK set expression equals the DPof/QPof operators (clean context).
THEOREM SetEqHelper ==
  ASSUME NEW rr, NEW A1D, NEW A1Q
  PROVE  { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
            \union { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } }
         = DPof(A1D, rr) \union QPof(A1Q, rr)
  BY DEF DPof, QPof

\* Abstract the message set into a fresh `mset` so the Variant reasoning never sees the
\* poisoning `msgs2[rr]` term. SUFFICES does the \E-elimination and goal rewrite.
THEOREM ShapeFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsD2(m) => AsD2(m).r = rr
  <1> SUFFICES ASSUME NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                      NEW A1Q \in SUBSET [ src: ALL, r: ROUNDS ],
                      mset = DPof(A1D, rr) \union QPof(A1Q, rr)
               PROVE  \A m \in mset : IsD2(m) => AsD2(m).r = rr
        OBVIOUS
  <1>1. SUFFICES \A m \in DPof(A1D, rr) \union QPof(A1Q, rr) :
                   IsD2(m) => AsD2(m).r = rr
        OBVIOUS
  <1> QED BY ShapeHelper

\* Decomposition of msgs2[rr] from TypeOK as a SMALL existential (DPof/QPof opaque).
\* The heavy `msgs2 = [...]` PICK is kept LOCAL to this proof so it never pollutes callers.
THEOREM Msgs2Decomp ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              msgs2[rr] = DPof(A1D, rr) \union QPof(A1Q, rr)
  <1> PICK B1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
           B1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
        msgs2 = [ r \in ROUNDS |->
            { D2(mm.src, r, mm.v): mm \in { m \in B1D: m.r = r } }
                \union { Q2(mm.src, r): mm \in { m \in B1Q: m.r = r } } ]
        BY DEF TypeOK
  <1>1. msgs2[rr] = { D2(mm.src, rr, mm.v): mm \in { m \in B1D: m.r = rr } }
                 \union { Q2(mm.src, rr): mm \in { m \in B1Q: m.r = rr } }
        OBVIOUS
  <1>2. msgs2[rr] = DPof(B1D, rr) \union QPof(B1Q, rr) BY <1>1, SetEqHelper
  <1> QED BY <1>2

\* The round invariant, fully proved.
THEOREM Msgs2Shape ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsD2(m) => AsD2(m).r = rr
  BY Msgs2Decomp, ShapeFromExists

\* --- src \in ALL variant (needed to bound D2 senders) ---
THEOREM ShapeHelperSrc ==
  ASSUME NEW rr, NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ], NEW A1Q, NEW m,
         m \in DPof(A1D, rr) \union QPof(A1Q, rr), IsD2(m)
  PROVE  AsD2(m).src \in ALL
  <1>1. m \notin QPof(A1Q, rr)
        <2> SUFFICES ASSUME m \in QPof(A1Q, rr) PROVE FALSE OBVIOUS
        <2>1. PICK mq \in { m \in A1Q: m.r = rr } : m = Q2(mq.src, rr) BY DEF QPof
        <2> QED BY <2>1, VariantAx
  <1>2. PICK md \in { m \in A1D: m.r = rr } : m = D2(md.src, rr, md.v) BY <1>1 DEF DPof
  <1>3. md \in A1D BY <1>2
  <1> QED BY <1>2, <1>3, VariantAx

THEOREM ShapeSrcFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] : mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsD2(m) => AsD2(m).src \in ALL
  <1> SUFFICES ASSUME NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                      NEW A1Q \in SUBSET [ src: ALL, r: ROUNDS ],
                      mset = DPof(A1D, rr) \union QPof(A1Q, rr)
               PROVE  \A m \in mset : IsD2(m) => AsD2(m).src \in ALL
        OBVIOUS
  <1>1. SUFFICES \A m \in DPof(A1D, rr) \union QPof(A1Q, rr) : IsD2(m) => AsD2(m).src \in ALL
        OBVIOUS
  <1> QED BY ShapeHelperSrc

THEOREM Msgs2SrcInAll ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsD2(m) => AsD2(m).src \in ALL
  BY Msgs2Decomp, ShapeSrcFromExists

\* Type-1 message shape from TypeOK (simpler than msgs2: no Variants).
THEOREM Msgs1Shape ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs1[rr] : m.r = rr /\ m.src \in ALL
  <1> PICK A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
        msgs1 = [ r \in ROUNDS |-> { m \in A1 : m.r = r } ]
        BY DEF TypeOK
  <1>1. msgs1[rr] = { m \in A1 : m.r = rr } OBVIOUS
  <1> QED BY <1>1

THEOREM Msgs1DomR ==
  ASSUME TypeOK PROVE DOMAIN msgs1 = ROUNDS
  <1> PICK A1 : msgs1 = [ r \in ROUNDS |-> { m \in A1 : m.r = r } ] BY DEF TypeOK
  <1> QED OBVIOUS

\* Type-2 message round shape (both D2 and Q2): the round field equals the index.
THEOREM ShapeHelperR ==
  ASSUME NEW rr, NEW A1D, NEW A1Q, NEW m, m \in DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
  <1>1. CASE m \in DPof(A1D, rr)
        <2>1. PICK md \in { m \in A1D : m.r = rr } : m = D2(md.src, rr, md.v) BY <1>1 DEF DPof
        <2> QED BY <2>1, VariantAx
  <1>2. CASE m \in QPof(A1Q, rr)
        <2>1. PICK mq \in { m \in A1Q : m.r = rr } : m = Q2(mq.src, rr) BY <1>2 DEF QPof
        <2> QED BY <2>1, VariantAx
  <1> QED BY <1>1, <1>2

THEOREM ShapeRFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] : mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
  <1> SUFFICES ASSUME NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                      NEW A1Q \in SUBSET [ src: ALL, r: ROUNDS ],
                      mset = DPof(A1D, rr) \union QPof(A1Q, rr)
               PROVE  \A m \in mset : (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
        OBVIOUS
  <1>1. SUFFICES \A m \in DPof(A1D, rr) \union QPof(A1Q, rr) :
                   (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
        OBVIOUS
  <1> QED BY ShapeHelperR

THEOREM Msgs2RShape ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
  BY Msgs2Decomp, ShapeRFromExists

THEOREM Msgs2DomR ==
  ASSUME TypeOK PROVE DOMAIN msgs2 = ROUNDS
  <1> PICK B1D, B1Q :
        msgs2 = [ r \in ROUNDS |-> { D2(mm.src, r, mm.v): mm \in { m \in B1D: m.r = r } }
                      \union { Q2(mm.src, r): mm \in { m \in B1Q: m.r = r } } ]
        BY DEF TypeOK
  <1> QED OBVIOUS

\*****************************************************************************
\* D2-MESSAGE COUNTING for a fixed (round, value): the set DvSet(r,v) of all D2(v)
\* messages is finite (injects into ALL via sender), and at least one has a CORRECT
\* sender when it has >= T+1 messages (faulty ones number <= F via FaultyD2Bound).
\*****************************************************************************
DvSet(r, v) == { m \in msgs2[r] : IsD2(m) /\ AsD2(m).v = v }
DvFn(r, v) == [ m \in DvSet(r, v) |-> AsD2(m).src ]

THEOREM DvInjective ==
  ASSUME NEW r, NEW v, \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r,
         NEW a \in DvSet(r, v), NEW b \in DvSet(r, v), DvFn(r, v)[a] = DvFn(r, v)[b]
  PROVE  a = b
  BY Zenon, VariantAx DEF DvSet, DvFn

THEOREM D2SetFinite ==
  ASSUME TypeOK, NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  IsFiniteSet(DvSet(r, v)) /\ Cardinality(DvSet(r, v)) <= N
  <1>r. \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r BY Msgs2Shape
  <1>s. \A m \in msgs2[r] : IsD2(m) => AsD2(m).src \in ALL BY Msgs2SrcInAll
  <1>1. DvFn(r, v) \in [ DvSet(r, v) -> ALL ] BY <1>s DEF DvSet, DvFn
  <1>2. \A a, b \in DvSet(r, v) : DvFn(r, v)[a] = DvFn(r, v)[b] => a = b BY <1>r, DvInjective
  <1>3. DvFn(r, v) \in Injection(DvSet(r, v), ALL) BY <1>1, <1>2 DEF Injection, IsInjective
  <1>4. IsFiniteSet(DvSet(r, v)) /\ Cardinality(DvSet(r, v)) <= Cardinality(ALL)
        BY <1>3, ALL_Card, FS_Injection
  <1> QED BY <1>4, ALL_Card

\* Abstract arithmetic: >= T+1 elements, <= F of them excluded, leaves >= 1.
LEMMA Arith_DiffPos ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a >= T + 1, b <= F
  PROVE  a - b >= 1
  BY FleqT, ConstNat

\* A D2 quorum of >= T+1 messages contains one from a CORRECT replica.
THEOREM CorrectD2Exists ==
  ASSUME TypeOK, NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(DvSet(r, v)) >= T + 1
  PROVE  \E mv \in msgs2[r] : IsD2(mv) /\ AsD2(mv).v = v /\ AsD2(mv).src \in CORRECT
  <1>r. \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r BY Msgs2Shape
  <1>s. \A m \in msgs2[r] : IsD2(m) => AsD2(m).src \in ALL BY Msgs2SrcInAll
  <1>fin. IsFiniteSet(DvSet(r, v)) BY D2SetFinite
  <1>sub. FaultyD2(r, v) \subseteq DvSet(r, v) BY DEF FaultyD2, DvSet
  <1>fin2. IsFiniteSet(FaultyD2(r, v)) BY <1>fin, <1>sub, FS_Subset
  <1>fd. Cardinality(FaultyD2(r, v)) <= F BY <1>r, FaultyD2Bound
  <1>int. DvSet(r, v) \cap FaultyD2(r, v) = FaultyD2(r, v) BY <1>sub
  <1>diff. Cardinality(DvSet(r, v) \ FaultyD2(r, v))
              = Cardinality(DvSet(r, v)) - Cardinality(FaultyD2(r, v))
           BY <1>fin, <1>int, FS_Difference
  <1>card. Cardinality(DvSet(r, v)) \in Nat /\ Cardinality(FaultyD2(r, v)) \in Nat
           BY <1>fin, <1>fin2, FS_CardinalityType
  <1>arith. Cardinality(DvSet(r, v)) - Cardinality(FaultyD2(r, v)) >= 1
            BY <1>card, <1>fd, Arith_DiffPos
  <1>pos. Cardinality(DvSet(r, v) \ FaultyD2(r, v)) >= 1 BY <1>diff, <1>arith
  <1>ne. DvSet(r, v) \ FaultyD2(r, v) # {}
         <2> SUFFICES ASSUME DvSet(r, v) \ FaultyD2(r, v) = {} PROVE FALSE OBVIOUS
         <2>1. IsFiniteSet(DvSet(r, v) \ FaultyD2(r, v)) BY <1>fin, FS_Difference
         <2> QED BY <2>1, <1>pos, FS_EmptySet
  <1>pick. PICK mv \in DvSet(r, v) : mv \notin FaultyD2(r, v) BY <1>ne
  <1>cor. AsD2(mv).src \in CORRECT
          <2>1. AsD2(mv).src \in ALL BY <1>s, <1>pick DEF DvSet
          <2>2. AsD2(mv).src \notin FAULTY BY <1>pick DEF DvSet, FaultyD2
          <2> QED BY <2>1, <2>2 DEF ALL
  <1> QED BY <1>pick, <1>cor DEF DvSet

\* The state tuple (the spec defines no `vars`; we provide one for [Next]_vars).
vars == << value, decision, round, step, msgs1, msgs2 >>

THEOREM TypeOKPrimeIntro ==
  ASSUME value' \in [ CORRECT -> VALUES ],
         decision' \in [ CORRECT -> VALUES \union { NO_DECISION } ],
         round' \in [ CORRECT -> ROUNDS ],
         step' \in [ CORRECT -> { S1, S2, S3 } ],
         \E A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
           msgs1' = [ r \in ROUNDS |-> { m \in A1 : m.r = r } ],
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
             A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
           msgs2' = [ r \in ROUNDS |->
             { D2(mm.src, r, mm.v): mm \in { m \in A1D: m.r = r } }
               \union { Q2(mm.src, r): mm \in { m \in A1Q: m.r = r } } ]
  PROVE  TypeOK'
  BY DEF TypeOK

THEOREM Msgs2PrimeWitnessIntro ==
  ASSUME NEW AD \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW AQ \in SUBSET [ src: ALL, r: ROUNDS ],
         msgs2' = [ rr \in ROUNDS |->
           { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
             \union { Q2(mm.src, rr): mm \in { m \in AQ: m.r = rr } } ]
  PROVE  \E B1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            B1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
          msgs2' = [ rr \in ROUNDS |->
            { D2(mm.src, rr, mm.v): mm \in { m \in B1D: m.r = rr } }
              \union { Q2(mm.src, rr): mm \in { m \in B1Q: m.r = rr } } ]
  OBVIOUS

THEOREM Msgs1AddOneRep ==
  ASSUME NEW A \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW rr0 \in ROUNDS,
         NEW src0 \in ALL,
         NEW val0 \in VALUES,
         NEW f,
         f = [ rr \in ROUNDS |-> { m \in A : m.r = rr } ]
  PROVE  [ f EXCEPT ![rr0] = f[rr0] \union { M1(src0, rr0, val0) } ]
         = [ rr \in ROUNDS |->
              { m \in A \union { M1(src0, rr0, val0) } : m.r = rr } ]
  <1> DEFINE lhs == [ f EXCEPT ![rr0] = f[rr0] \union { M1(src0, rr0, val0) } ]
             rhs == [ rr \in ROUNDS |->
                       { m \in A \union { M1(src0, rr0, val0) } : m.r = rr } ]
  <1>vals. \A rr \in ROUNDS : lhs[rr] = rhs[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE lhs[rr] = rhs[rr] OBVIOUS
    <2>m1r. M1(src0, rr0, val0).r = rr0 BY DEF M1
    <2>eq. CASE rr = rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>eq, <2>m1r, SMT DEF lhs, rhs, M1
    <2>ne. CASE rr # rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>ne, <2>m1r, SMT DEF lhs, rhs, M1
    <2> QED BY <2>eq, <2>ne
  <1> QED BY <1>vals DEF lhs, rhs

THEOREM Msgs2AddDRep ==
  ASSUME NEW AD \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW AQ \in SUBSET [ src: ALL, r: ROUNDS ],
         NEW rr0 \in ROUNDS,
         NEW src0 \in ALL,
         NEW val0 \in VALUES,
         NEW f,
         f = [ rr \in ROUNDS |->
               { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
                 \union { Q2(mm.src, rr): mm \in { m \in AQ: m.r = rr } } ]
  PROVE  [ f EXCEPT ![rr0] = f[rr0] \union { D2(src0, rr0, val0) } ]
         = [ rr \in ROUNDS |->
             { D2(mm.src, rr, mm.v):
                 mm \in { m \in AD \union { [ src |-> src0, r |-> rr0, v |-> val0 ] }:
                   m.r = rr } }
               \union { Q2(mm.src, rr): mm \in { m \in AQ: m.r = rr } } ]
  <1> DEFINE lhs == [ f EXCEPT ![rr0] = f[rr0] \union { D2(src0, rr0, val0) } ]
             rhs == [ rr \in ROUNDS |->
               { D2(mm.src, rr, mm.v):
                   mm \in { m \in AD \union { [ src |-> src0, r |-> rr0, v |-> val0 ] }:
                     m.r = rr } }
                 \union { Q2(mm.src, rr): mm \in { m \in AQ: m.r = rr } } ]
  <1>vals. \A rr \in ROUNDS : lhs[rr] = rhs[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE lhs[rr] = rhs[rr] OBVIOUS
    <2>newr. [ src |-> src0, r |-> rr0, v |-> val0 ].r = rr0 OBVIOUS
    <2>eq. CASE rr = rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>eq, <2>newr, VariantAx, SMT DEF lhs, rhs, D2
    <2>ne. CASE rr # rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>ne, <2>newr, VariantAx, SMT DEF lhs, rhs, D2
    <2> QED BY <2>eq, <2>ne
  <1> QED BY <1>vals DEF lhs, rhs

THEOREM Msgs2AddQRep ==
  ASSUME NEW AD \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW AQ \in SUBSET [ src: ALL, r: ROUNDS ],
         NEW rr0 \in ROUNDS,
         NEW src0 \in ALL,
         NEW f,
         f = [ rr \in ROUNDS |->
               { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
                 \union { Q2(mm.src, rr): mm \in { m \in AQ: m.r = rr } } ]
  PROVE  [ f EXCEPT ![rr0] = f[rr0] \union { Q2(src0, rr0) } ]
         = [ rr \in ROUNDS |->
             { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
               \union { Q2(mm.src, rr):
                 mm \in { m \in AQ \union { [ src |-> src0, r |-> rr0 ] }:
                   m.r = rr } } ]
  <1> DEFINE lhs == [ f EXCEPT ![rr0] = f[rr0] \union { Q2(src0, rr0) } ]
             rhs == [ rr \in ROUNDS |->
               { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
                 \union { Q2(mm.src, rr):
                   mm \in { m \in AQ \union { [ src |-> src0, r |-> rr0 ] }:
                     m.r = rr } } ]
  <1>vals. \A rr \in ROUNDS : lhs[rr] = rhs[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE lhs[rr] = rhs[rr] OBVIOUS
    <2>newr. [ src |-> src0, r |-> rr0 ].r = rr0 OBVIOUS
    <2>eq. CASE rr = rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>eq, <2>newr, VariantAx, SMT DEF lhs, rhs, Q2
    <2>ne. CASE rr # rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>ne, <2>newr, VariantAx, SMT DEF lhs, rhs, Q2
    <2> QED BY <2>eq, <2>ne
  <1> QED BY <1>vals DEF lhs, rhs

\*****************************************************************************
\* FAULTY-STEP CONSEQUENCES.
\* `DEF FaultyStep` cannot be discharged by any backend (the SMT encoder aborts on the
\* two-variable set comprehension `{ D2(src,r,v): src \in FAULTY, v \in VALUES }`, and
\* Zenon/Isabelle fail). We therefore state FaultyStep's relevant CONSEQUENCES -- which
\* avoid that construct -- as a single admitted theorem, and prove every per-lemma
\* FaultyStep case from it. The consequences are: the per-replica state is unchanged, the
\* message buffers only grow, and every newly added message has a FAULTY sender.
\* (All provable from DEF FaultyStep on a tlapm whose encoder handles the construct.)
\*****************************************************************************
THEOREM FaultyStepProps ==
  ASSUME FaultyStep
  PROVE  /\ value' = value /\ decision' = decision /\ round' = round /\ step' = step
         /\ \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr] /\ msgs2[rr] \subseteq msgs2'[rr]
         /\ \A rr \in ROUNDS : \A m \in msgs1'[rr] : m \notin msgs1[rr] => m.src \in FAULTY
         /\ \A rr \in ROUNDS : \A m \in msgs2'[rr] :
              m \notin msgs2[rr] =>
                ((IsD2(m) => AsD2(m).src \in FAULTY) /\ (IsQ2(m) => AsQ2(m).src \in FAULTY))
  OMITTED \* see note above: provable from DEF FaultyStep; admitted due to a tlapm encoder limit

\*****************************************************************************
\* SECTION B -- TYPE PRESERVATION + BASE CASE
\*****************************************************************************

\* BASE CASE. With empty message buffers, no decision, round 1 and step S1,
\* every conjunct of IndInv is vacuous or trivially true.
THEOREM InitInd == Init => TypeOK /\ IndInv
  <1> SUFFICES ASSUME Init PROVE TypeOK /\ IndInv
        OBVIOUS
  <1> USE DEF Init
  <1>m1. \A r \in ROUNDS : msgs1[r] = {}
        OBVIOUS
  <1>m2. \A r \in ROUNDS : msgs2[r] = {}
        OBVIOUS
  \* --- TypeOK ---
  <1>type. TypeOK
    <2>1. value \in [ CORRECT -> VALUES ]
          OBVIOUS
    <2>2. decision \in [ CORRECT -> VALUES \union { NO_DECISION } ]
          OBVIOUS
    <2>3. round \in [ CORRECT -> ROUNDS ]
          BY RoundsNat
    <2>4. step \in [ CORRECT -> { S1, S2, S3 } ]
          OBVIOUS
    <2>5. \E A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ]:
              msgs1 = [ r \in ROUNDS |-> { m \in A1: m.r = r } ]
          <3> WITNESS {} \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ]
          <3> QED OBVIOUS
    <2>6. \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
              A1Q \in SUBSET [ src: ALL, r: ROUNDS ]:
              msgs2 = [ r \in ROUNDS |->
                  { D2(mm.src, r, mm.v): mm \in { m \in A1D: m.r = r } }
                      \union { Q2(mm.src, r): mm \in { m \in A1Q: m.r = r } } ]
          <3> WITNESS {} \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                      {} \in SUBSET [ src: ALL, r: ROUNDS ]
          <3> QED OBVIOUS
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK
  \* --- IndInv: each lemma holds because msgs are empty / round = 1 / no decision ---
  <1>L2. Lemma2_NoEquivocation1ByCorrect
        BY <1>m1 DEF Lemma2_NoEquivocation1ByCorrect
  <1>L3. Lemma3_NoEquivocation2ByCorrect
        BY <1>m2 DEF Lemma3_NoEquivocation2ByCorrect
  <1>L4. Lemma4_MessagesNotFromFuture
        BY <1>m1, <1>m2 DEF Lemma4_MessagesNotFromFuture
  <1>L5. Lemma5_RoundNeedsSentMessages
        \* round=1, step=S1: positive rounds rule out r < myRound.
        <2> SUFFICES ASSUME NEW id \in CORRECT, NEW r \in ROUNDS
              PROVE /\ (r < round[id] \/ (r = round[id] /\ step[id] /= S1))
                       => (\E m \in msgs1[r] : m.src = id)
                    /\ (r < round[id])
                       => (\E m \in msgs2[r] : AsD2(m).src = id \/ AsQ2(m).src = id)
                    /\ (r = round[id] /\ step[id] = S3)
                       => (\E m \in msgs2[r] : AsD2(m).src = id \/ AsQ2(m).src = id)
            BY DEF Lemma5_RoundNeedsSentMessages
        <2>pos. r \in Nat /\ r >= 1 BY RoundPos
        <2>st. round[id] = 1 /\ step[id] = S1 BY DEF Init
        <2>dist. S1 # S3 BY DEF S1, S3
        <2>notlt. ~(r < round[id]) BY <2>pos, <2>st, Arith_PosNotLtOne
        <2>c1. (r < round[id] \/ (r = round[id] /\ step[id] /= S1))
                 => (\E m \in msgs1[r] : m.src = id)
          <3> SUFFICES ASSUME r < round[id] \/ (r = round[id] /\ step[id] /= S1)
                       PROVE  FALSE
                OBVIOUS
          <3>1. CASE r < round[id] BY <3>1, <2>notlt
          <3>2. CASE r = round[id] /\ step[id] /= S1 BY <3>2, <2>st
          <3> QED BY <3>1, <3>2
        <2>c2. (r < round[id])
                 => (\E m \in msgs2[r] : AsD2(m).src = id \/ AsQ2(m).src = id)
          <3> SUFFICES ASSUME r < round[id] PROVE FALSE OBVIOUS
          <3> QED BY <2>notlt
        <2>c3. (r = round[id] /\ step[id] = S3)
                 => (\E m \in msgs2[r] : AsD2(m).src = id \/ AsQ2(m).src = id)
          <3> SUFFICES ASSUME r = round[id], step[id] = S3 PROVE FALSE OBVIOUS
          <3> QED BY <2>st, <2>dist
        <2> QED BY <2>c1, <2>c2, <2>c3
  <1>L6. Lemma6_DecisionDefinesValue
        BY DEF Lemma6_DecisionDefinesValue
  <1>L7. Lemma7_D2RequiresQuorum
        BY <1>m2 DEF Lemma7_D2RequiresQuorum
  <1>L8. Lemma8_Q2RequiresNoQuorumFaster
        BY <1>m2 DEF Lemma8_Q2RequiresNoQuorumFaster
  <1>L9. Lemma9_RoundsConnection
        BY <1>m2 DEF Lemma9_RoundsConnection, SupportedValues
  <1>L10. Lemma10_M1RequiresQuorum
        BY <1>m1 DEF Lemma10_M1RequiresQuorum
  <1>L11. Lemma11_ValueOnQuorumLessRam
        \* round[id] = 1, so the r > 1 premise is false.
        BY DEF Lemma11_ValueOnQuorumLessRam
  <1>L12. Lemma12_CannotJumpRoundsWithoutQuorum
        \* nextRoundReached at r with r+1=1 would require r=0, not a positive round.
        BY <1>m2, RoundPos DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1>L13. Lemma13_ValueLock
        BY DEF Lemma13_ValueLock
  <1>L1. Lemma1_DecisionRequiresLastQuorumLessRam
        BY DEF Lemma1_DecisionRequiresLastQuorumLessRam
  <1> QED
        BY <1>type, <1>L1, <1>L2, <1>L3, <1>L4, <1>L5, <1>L6, <1>L7, <1>L8,
           <1>L9, <1>L10, <1>L11, <1>L12, <1>L13 DEF IndInv

\* TYPE PRESERVATION. Each action keeps every variable in its declared type and
\* keeps msgs1/msgs2 in the existential "shape" required by TypeOK.
THEOREM TypePres ==
  ASSUME TypeOK, [Next]_vars
  PROVE  TypeOK'
  <1> USE DEF vars
  <1>1. CASE UNCHANGED vars
        BY <1>1 DEF TypeOK, vars
  <1>2. CASE CorrectStep
    <2>1. PICK id \in CORRECT : Step1(id) \/ Step2(id) \/ Step3(id)
          BY <1>2 DEF CorrectStep
    <2>2. CASE Step1(id)
          \* msgs1[r] gains M1(id,r,value[id]); reuse TypeOK witness A1 \cup {that msg}.
      <3> PICK A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
            msgs1 = [ rr \in ROUNDS |-> { m \in A1 : m.r = rr } ]
          BY DEF TypeOK
      <3> PICK A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
            msgs2 = [ rr \in ROUNDS |->
              { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
                \union { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } } ]
          BY DEF TypeOK
      <3> DEFINE A1p == A1 \union { M1(id, round[id], value[id]) }
      <3>fr. /\ value' = value /\ decision' = decision /\ round' = round /\ msgs2' = msgs2
              /\ step' = [ step EXCEPT ![id] = S2 ]
              /\ msgs1' = [ msgs1 EXCEPT
                   ![round[id]] = msgs1[round[id]] \union { M1(id, round[id], value[id]) } ]
          BY <2>2 DEF Step1
      <3>r0. round[id] \in ROUNDS /\ value[id] \in VALUES
          BY DEF TypeOK
      <3>idall. id \in ALL BY DEF ALL
      <3>1. value' \in [ CORRECT -> VALUES ] BY <3>fr DEF TypeOK
      <3>2. decision' \in [ CORRECT -> VALUES \union { NO_DECISION } ] BY <3>fr DEF TypeOK
      <3>3. round' \in [ CORRECT -> ROUNDS ] BY <3>fr DEF TypeOK
      <3>4. step' \in [ CORRECT -> { S1, S2, S3 } ] BY <3>fr DEF TypeOK, S2
      <3>5. \E B1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
              msgs1' = [ rr \in ROUNDS |-> { m \in B1 : m.r = rr } ]
        <4>1. A1p \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ]
              BY <3>r0, <3>idall DEF A1p, M1
        <4>2. msgs1' = [ rr \in ROUNDS |-> { m \in A1p : m.r = rr } ]
              BY <2>2, <3>fr, <3>r0, <3>idall, Msgs1AddOneRep DEF A1p, Step1
        <4> QED BY <4>1, <4>2
      <3>6. \E B1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                B1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              msgs2' = [ rr \in ROUNDS |->
                { D2(mm.src, rr, mm.v): mm \in { m \in B1D: m.r = rr } }
                  \union { Q2(mm.src, rr): mm \in { m \in B1Q: m.r = rr } } ]
        <4> QED BY <3>fr
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF TypeOK
    <2>3. CASE Step2(id)
          \* msgs2[r] gains D2(id,r,v) or Q2(id,r); reuse/extend the msgs2 witnesses.
      <3> PICK A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
            msgs1 = [ rr \in ROUNDS |-> { m \in A1 : m.r = rr } ]
          BY DEF TypeOK
      <3> PICK A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
            msgs2 = [ rr \in ROUNDS |->
              { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
                \union { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } } ]
          BY DEF TypeOK
      <3>fr. /\ value' = value /\ decision' = decision /\ round' = round /\ msgs1' = msgs1
              /\ step' = [ step EXCEPT ![id] = S3 ]
          BY <2>3 DEF Step2
      <3>r0. round[id] \in ROUNDS
          BY DEF TypeOK
      <3>idall. id \in ALL BY DEF ALL
      <3>1. value' \in [ CORRECT -> VALUES ] BY <3>fr DEF TypeOK
      <3>2. decision' \in [ CORRECT -> VALUES \union { NO_DECISION } ] BY <3>fr DEF TypeOK
      <3>3. round' \in [ CORRECT -> ROUNDS ] BY <3>fr DEF TypeOK
      <3>4. step' \in [ CORRECT -> { S1, S2, S3 } ] BY <3>fr DEF TypeOK, S3
      <3>5. \E B1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
              msgs1' = [ rr \in ROUNDS |-> { m \in B1 : m.r = rr } ]
        <4> QED BY <3>fr
      <3>6. \E B1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                B1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              msgs2' = [ rr \in ROUNDS |->
                { D2(mm.src, rr, mm.v): mm \in { m \in B1D: m.r = rr } }
                  \union { Q2(mm.src, rr): mm \in { m \in B1Q: m.r = rr } } ]
        <4> PICK received \in SUBSET msgs1[round[id]] :
              /\ Cardinality(Senders1(received)) >= N - T
              /\ LET Weights == [ v \in VALUES |->
                   Cardinality(Senders1({ m \in received: m.v = v })) ]
                 IN
                 \/ \E v \in VALUES:
                      /\ 2 * Weights[v] > N + T
                      /\ msgs2' =
                           [ msgs2 EXCEPT ![round[id]] =
                               msgs2[round[id]] \union { D2(id, round[id], v) } ]
                 \/ /\ \A v \in VALUES: 2 * Weights[v] <= N + T
                    /\ msgs2' =
                         [ msgs2 EXCEPT ![round[id]] =
                             msgs2[round[id]] \union { Q2(id, round[id]) } ]
            BY <2>3 DEF Step2
        <4> DEFINE Weights == [ v \in VALUES |->
                   Cardinality(Senders1({ m \in received: m.v = v })) ]
        <4>d. CASE \E v \in VALUES:
                  /\ 2 * Weights[v] > N + T
                  /\ msgs2' =
                       [ msgs2 EXCEPT ![round[id]] =
                           msgs2[round[id]] \union { D2(id, round[id], v) } ]
          <5> PICK v \in VALUES:
                /\ 2 * Weights[v] > N + T
                /\ msgs2' =
                     [ msgs2 EXCEPT ![round[id]] =
                         msgs2[round[id]] \union { D2(id, round[id], v) } ]
              BY <4>d
          <5> DEFINE A1Dp == A1D \union { [ src |-> id, r |-> round[id], v |-> v ] }
          <5>1. A1Dp \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ]
                BY <3>r0, <3>idall DEF A1Dp
          <5>2. msgs2' = [ rr \in ROUNDS |->
                  { D2(mm.src, rr, mm.v): mm \in { m \in A1Dp: m.r = rr } }
                    \union { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } } ]
                BY <4>d, <3>r0, <3>idall, Msgs2AddDRep DEF A1Dp, Step2
          <5>qok. A1Q \in SUBSET [ src: ALL, r: ROUNDS ] OBVIOUS
          <5> QED BY <5>1, <5>2, <5>qok, Msgs2PrimeWitnessIntro
        <4>q. CASE /\ \A v \in VALUES: 2 * Weights[v] <= N + T
                    /\ msgs2' =
                         [ msgs2 EXCEPT ![round[id]] =
                             msgs2[round[id]] \union { Q2(id, round[id]) } ]
          <5> DEFINE A1Qp == A1Q \union { [ src |-> id, r |-> round[id] ] }
          <5>1. A1Qp \in SUBSET [ src: ALL, r: ROUNDS ]
                BY <3>r0, <3>idall DEF A1Qp
          <5>2. msgs2' = [ rr \in ROUNDS |->
                  { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
                    \union { Q2(mm.src, rr): mm \in { m \in A1Qp: m.r = rr } } ]
                BY <4>q, <3>r0, <3>idall, Msgs2AddQRep DEF A1Qp, Step2
          <5>dok. A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] OBVIOUS
          <5> QED BY <5>dok, <5>1, <5>2, Msgs2PrimeWitnessIntro
        <4> QED BY <4>d, <4>q
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF TypeOK
    <2>4. CASE Step3(id)
          \* value/decision/round/step updates stay in type; msgs unchanged.
          BY <2>4, RoundsNat DEF TypeOK, Step3
    <2> QED BY <2>1, <2>2, <2>3, <2>4
  <1>3. CASE FaultyStep
        \* faulty replicas add messages with src \in FAULTY \subseteq ALL.
        OMITTED \* TODO: FaultyStep's arbitrary D2/Q2 set-map hits the same tlapm encoder limit as FaultyStepProps.
  <1> QED
        BY <1>1, <1>2, <1>3 DEF Next

\*****************************************************************************
\* SECTION C -- INDUCTIVE STEP (one preservation theorem per lemma)
\*
\* Uniform shape: ASSUME TypeOK, IndInv, [Next]_vars PROVE Lemma_i'.
\* Case split: stutter (UNCHANGED vars) / Step1 / Step2 / Step3 / FaultyStep, written
\* as a FLAT set of ASSUME/PROVE cases so the [Next]_vars assumption is in scope at the
\* combining QED. "Frame" cases (the action leaves all variables the lemma mentions
\* unchanged) are discharged from the action definition; substantive cases are OMITTED
\* with a TODO naming the cardinality/quorum fact required.
\*****************************************************************************

\* ===== L2: no type-1 equivocation by correct (msgs1) =====
THEOREM Pres_L2_S2 ==
  ASSUME IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma2_NoEquivocation1ByCorrect'
  BY DEF IndInv, Lemma2_NoEquivocation1ByCorrect, Step2
THEOREM Pres_L2_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma2_NoEquivocation1ByCorrect'
  BY DEF IndInv, Lemma2_NoEquivocation1ByCorrect, Step3
THEOREM Pres_L2_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma2_NoEquivocation1ByCorrect'
  BY DEF IndInv, Lemma2_NoEquivocation1ByCorrect, vars
\* The substantive Step1 case: the new M1(id,r,value[id]) is the only round-r message from
\* id (Lemma4: id is in S1, so it has not sent at its current round), so no equivocation.
THEOREM Pres_L2_S1 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma2_NoEquivocation1ByCorrect'
  <1> USE DEF IndInv
  <1>r0. round[id] \in ROUNDS BY DEF TypeOK
  <1>dom. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>meq. msgs1' = [ msgs1 EXCEPT
            ![round[id]] = msgs1[round[id]] \union { M1(id, round[id], value[id]) } ]
          BY DEF Step1
  <1>nf. \A m \in msgs1[round[id]] : m.src /= id
    <2> SUFFICES ASSUME NEW m \in msgs1[round[id]], m.src = id PROVE FALSE OBVIOUS
    <2>1. step[id] = S1 BY DEF Step1
    <2>2. m.r < round[id] BY <2>1, <1>r0 DEF Lemma4_MessagesNotFromFuture
    <2>3. m.r = round[id] BY <1>r0, Msgs1Shape
    <2> QED BY <2>2, <2>3
  <1> SUFFICES ASSUME NEW r \in ROUNDS, NEW p1 \in msgs1'[r], NEW p2 \in msgs1'[r],
                      p1.src \in CORRECT, p1.src = p2.src
               PROVE  p1.v = p2.v
        BY DEF Lemma2_NoEquivocation1ByCorrect
  <1>nsrc. M1(id, round[id], value[id]).src = id BY DEF M1
  <1>A. CASE r # round[id]
        <2>1. msgs1'[r] = msgs1[r] BY <1>meq, <1>dom, <1>r0, <1>A
        <2> QED BY <2>1 DEF Lemma2_NoEquivocation1ByCorrect
  <1>B. CASE r = round[id]
        <2>1. msgs1'[r] = msgs1[round[id]] \union { M1(id, round[id], value[id]) }
              BY <1>meq, <1>dom, <1>r0, <1>B
        <2>p1. p1 \in msgs1[round[id]] \/ p1 = M1(id, round[id], value[id]) BY <2>1
        <2>p2. p2 \in msgs1[round[id]] \/ p2 = M1(id, round[id], value[id]) BY <2>1
        <2>2. CASE p1 \in msgs1[round[id]] /\ p2 \in msgs1[round[id]]
              BY <2>2, <1>B DEF Lemma2_NoEquivocation1ByCorrect
        <2>3. CASE p1 = M1(id, round[id], value[id])
              <3>1. p2.src = id BY <2>3, <1>nsrc
              <3>2. p2 = M1(id, round[id], value[id]) BY <3>1, <1>nf, <2>p2
              <3> QED BY <2>3, <3>2
        <2>4. CASE p2 = M1(id, round[id], value[id]) /\ p1 \in msgs1[round[id]]
              <3>1. p1.src = id BY <2>4, <1>nsrc
              <3> QED BY <3>1, <1>nf, <2>4
        <2> QED BY <2>p1, <2>p2, <2>2, <2>3, <2>4
  <1> QED BY <1>A, <1>B
\* FaultyStep case: new msgs1 messages have FAULTY src, so any CORRECT-sender message is
\* old; no new equivocation among correct senders.
THEOREM Pres_L2_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma2_NoEquivocation1ByCorrect'
  <1>l2. Lemma2_NoEquivocation1ByCorrect BY DEF IndInv
  <1>p. \A rr \in ROUNDS : \A m \in msgs1'[rr] : m \notin msgs1[rr] => m.src \in FAULTY
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW r \in ROUNDS, NEW m1 \in msgs1'[r], NEW m2 \in msgs1'[r],
                      m1.src \in CORRECT, m1.src = m2.src
               PROVE  m1.v = m2.v
        BY DEF Lemma2_NoEquivocation1ByCorrect
  <1>1. m1 \in msgs1[r] BY <1>p, DisjointCF
  <1>2. m2 \in msgs1[r] BY <1>p, DisjointCF
  <1> QED BY <1>1, <1>2, <1>l2 DEF Lemma2_NoEquivocation1ByCorrect
THEOREM Pres_Lemma2 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma2_NoEquivocation1ByCorrect'
  <1> QED BY Pres_L2_S1, Pres_L2_S2, Pres_L2_S3, Pres_L2_ST, Pres_L2_F DEF Next, CorrectStep

\* ===== L3: no type-2 equivocation by correct (msgs2) =====
THEOREM Pres_L3_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma3_NoEquivocation2ByCorrect'
  BY DEF IndInv, Lemma3_NoEquivocation2ByCorrect, Step1
THEOREM Pres_L3_S2 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma3_NoEquivocation2ByCorrect'
  <1>l3. Lemma3_NoEquivocation2ByCorrect BY DEF IndInv
  <1>l4. Lemma4_MessagesNotFromFuture BY DEF IndInv
  <1>r0. round[id] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>s2. step[id] = S2 BY DEF Step2
  <1>dist. S2 # S3 BY DEF S2, S3
  <1>nm. PICK nm :
        /\ msgs2' = [ msgs2 EXCEPT ![round[id]] = msgs2[round[id]] \union { nm } ]
        /\ (IF IsD2(nm) THEN AsD2(nm).src ELSE AsQ2(nm).src) = id
        /\ (IF IsD2(nm) THEN AsD2(nm).r ELSE AsQ2(nm).r) = round[id]
      BY VariantAx DEF Step2
  <1>noOld. \A m \in msgs2[round[id]] :
        (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) # id
    <2> SUFFICES ASSUME NEW m \in msgs2[round[id]],
                  (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) = id
          PROVE FALSE
        OBVIOUS
    <2>mr. (IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r) = round[id]
        BY <1>r0, Msgs2RShape, VariantAx
    <2>srcCor. (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) \in CORRECT
        OBVIOUS
    <2>srcEq. (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) = id
        OBVIOUS
    <2>notS3. step[(IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src)] # S3
        BY <2>srcEq, <1>s2, <1>dist
    <2>roundSrc. round[(IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src)] = round[id]
        BY <2>srcEq
    <2>lt. (IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r) < round[id]
        BY <1>l4, <1>r0, <2>srcCor, <2>notS3, <2>roundSrc DEF Lemma4_MessagesNotFromFuture
    <2> QED BY <2>mr, <2>lt
  <1> SUFFICES ASSUME NEW r \in ROUNDS, NEW m1 \in msgs2'[r], NEW m2 \in msgs2'[r]
        PROVE  /\ IsD2(m1) /\ IsD2(m2) /\ AsD2(m1).src = AsD2(m2).src =>
                  (AsD2(m1).src \in CORRECT => AsD2(m1).v = AsD2(m2).v)
               /\ IsQ2(m1) /\ IsD2(m2) /\ AsQ2(m1).src = AsD2(m2).src =>
                  AsQ2(m1).src \in FAULTY
      BY DEF Lemma3_NoEquivocation2ByCorrect
  <1> QED BY <1>l3, <1>nm, <1>noOld, <1>dom2, <1>r0, VariantAx
           DEF Lemma3_NoEquivocation2ByCorrect
THEOREM Pres_L3_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma3_NoEquivocation2ByCorrect'
  BY DEF IndInv, Lemma3_NoEquivocation2ByCorrect, Step3
THEOREM Pres_L3_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma3_NoEquivocation2ByCorrect'
  BY DEF IndInv, Lemma3_NoEquivocation2ByCorrect, vars
THEOREM Pres_L3_F ==
  ASSUME IndInv, FaultyStep
  PROVE  Lemma3_NoEquivocation2ByCorrect'
  BY FaultyStepProps, DisjointCF DEF IndInv, Lemma3_NoEquivocation2ByCorrect
THEOREM Pres_Lemma3 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma3_NoEquivocation2ByCorrect'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma3_NoEquivocation2ByCorrect'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma3_NoEquivocation2ByCorrect'
          OBVIOUS
    <2> QED BY Pres_L3_S2
  <1>o2. FaultyStep => Lemma3_NoEquivocation2ByCorrect'
    <2> SUFFICES ASSUME FaultyStep PROVE Lemma3_NoEquivocation2ByCorrect'
          OBVIOUS
    <2> QED BY Pres_L3_F
  <1> QED BY Pres_L3_S1, Pres_L3_S3, Pres_L3_ST, <1>o1, <1>o2 DEF Next, CorrectStep

\* ===== L4: messages not from the future =====
THEOREM Pres_L4_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma4_MessagesNotFromFuture'
  BY DEF IndInv, Lemma4_MessagesNotFromFuture, vars
\* Substantive Step1 case: the new M1 has round = round[id]; id moves S1->S2. We do NOT
\* USE DEF IndInv (it would expand the Cardinality-heavy lemmas and poison the arithmetic);
\* we extract just Lemma4. The step/round priming (step EXCEPT ![id]=S2) is handled by a
\* case split on whether the message's sender is id, with S1#S2#S3 distinctness and Nat
\* typing of message rounds (to get <= from <).
THEOREM Pres_L4_S1 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma4_MessagesNotFromFuture'
  <1>l4. Lemma4_MessagesNotFromFuture BY DEF IndInv
  <1>r0. round[id] \in ROUNDS /\ round[id] \in Nat BY RoundsNat DEF TypeOK
  <1>dom1. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>doms. step \in [ CORRECT -> { S1, S2, S3 } ] /\ round \in [ CORRECT -> ROUNDS ]
           BY DEF TypeOK
  <1>dist. S1 # S2 /\ S2 # S3 /\ S1 # S3 BY DEF S1, S2, S3
  <1>upd. /\ msgs1' = [ msgs1 EXCEPT
                ![round[id]] = msgs1[round[id]] \union { M1(id, round[id], value[id]) } ]
          /\ step' = [ step EXCEPT ![id] = S2 ] /\ round' = round /\ msgs2' = msgs2
          BY DEF Step1
  <1>s1. step[id] = S1 BY DEF Step1
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id THEN S2 ELSE step[x]) BY <1>upd, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = round[x] BY <1>upd, <1>doms
  <1> SUFFICES ASSUME NEW r \in ROUNDS
               PROVE  /\ \A m \in msgs1'[r] : m.src \in CORRECT =>
                          /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                          /\ step'[m.src] = S1 => (m.r < round'[m.src])
                      /\ \A m \in msgs2'[r] :
                          LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                              mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                          IN src \in CORRECT =>
                               /\ step'[src] = S3 => (mr <= round'[src])
                               /\ step'[src] /= S3 => (mr < round'[src])
        BY DEF Lemma4_MessagesNotFromFuture
  <1>P1. \A m \in msgs1'[r] : m.src \in CORRECT =>
            /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
            /\ step'[m.src] = S1 => (m.r < round'[m.src])
    <2> SUFFICES ASSUME NEW m \in msgs1'[r], m.src \in CORRECT
                 PROVE /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                       /\ step'[m.src] = S1 => (m.r < round'[m.src]) OBVIOUS
    <2>new. M1(id, round[id], value[id]) = [ src |-> id, r |-> round[id], v |-> value[id] ]
            BY DEF M1
    <2>1. m \in msgs1[r] \/ (r = round[id] /\ m = M1(id, round[id], value[id]))
          BY <1>upd, <1>dom1, <1>r0
    <2>2. CASE m \in msgs1[r]
          <3>a. CASE m.src = id
                <4>1. m.r < round[id] BY <3>a, <2>2, <1>l4, <1>s1 DEF Lemma4_MessagesNotFromFuture
                <4>nat. m.r \in Nat /\ round[id] \in Nat BY <2>2, Msgs1Shape, <1>r0, RoundsNat
                <4>2. step'[m.src] = S2 /\ round'[m.src] = round[id] BY <3>a, <1>st, <1>rd
                <4> QED BY <4>1, <4>nat, <4>2, <1>dist
          <3>b. CASE m.src # id
                <4>1. step'[m.src] = step[m.src] /\ round'[m.src] = round[m.src] BY <3>b, <1>st, <1>rd
                <4> QED BY <3>b, <2>2, <4>1, <1>l4 DEF Lemma4_MessagesNotFromFuture
          <3> QED BY <3>a, <3>b
    <2>3. CASE r = round[id] /\ m = M1(id, round[id], value[id])
          <3>1. m.src = id /\ m.r = round[id] BY <2>3, <2>new
          <3>2. step'[m.src] = S2 /\ round'[m.src] = round[id] BY <3>1, <1>st, <1>rd
          <3> QED BY <3>1, <3>2, <1>r0, <1>dist
    <2> QED BY <2>1, <2>2, <2>3
  <1>P2. \A m \in msgs2'[r] :
            LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
            IN src \in CORRECT =>
                 /\ step'[src] = S3 => (mr <= round'[src])
                 /\ step'[src] /= S3 => (mr < round'[src])
    <2> SUFFICES ASSUME NEW m \in msgs2'[r],
                  (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) \in CORRECT
                 PROVE LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                           mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                       IN /\ step'[src] = S3 => (mr <= round'[src])
                          /\ step'[src] /= S3 => (mr < round'[src]) OBVIOUS
    <2> DEFINE src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
    <2>old. m \in msgs2[r] BY <1>upd
    <2>a. CASE src = id
          <3>1. (IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r) < round[id]
                BY <2>a, <2>old, <1>l4, <1>s1, <1>dist DEF Lemma4_MessagesNotFromFuture
          <3>2. step'[src] = S2 /\ round'[src] = round[id] BY <2>a, <1>st, <1>rd
          <3> QED BY <3>1, <3>2, <1>dist
    <2>b. CASE src # id
          <3>1. step'[src] = step[src] /\ round'[src] = round[src] BY <2>b, <1>st, <1>rd
          <3> QED BY <2>b, <2>old, <3>1, <1>l4 DEF Lemma4_MessagesNotFromFuture
    <2> QED BY <2>a, <2>b
  <1> QED BY <1>P1, <1>P2
\* Substantive Step3 case: id advances round[id]->round[id]+1 and resets step to S1;
\* msgs1/msgs2 unchanged. Old bounds m.r <= round[id] become m.r < round[id]+1.
THEOREM Pres_L4_S3 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma4_MessagesNotFromFuture'
  <1>l4. Lemma4_MessagesNotFromFuture BY DEF IndInv
  <1>r0. round[id] \in ROUNDS /\ round[id] \in Nat BY RoundsNat DEF TypeOK
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dist. S1 # S2 /\ S2 # S3 /\ S1 # S3 BY DEF S1, S2, S3
  <1>upd. /\ round' = [ round EXCEPT ![id] = round[id] + 1 ]
          /\ step' = [ step EXCEPT ![id] = S1 ] /\ msgs1' = msgs1 /\ msgs2' = msgs2
          BY DEF Step3
  <1>s3. step[id] = S3 BY DEF Step3
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id THEN S1 ELSE step[x]) BY <1>upd, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = (IF x = id THEN round[id] + 1 ELSE round[x])
         BY <1>upd, <1>doms
  <1> SUFFICES ASSUME NEW r \in ROUNDS
               PROVE  /\ \A m \in msgs1'[r] : m.src \in CORRECT =>
                          /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                          /\ step'[m.src] = S1 => (m.r < round'[m.src])
                      /\ \A m \in msgs2'[r] :
                          LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                              mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                          IN src \in CORRECT =>
                               /\ step'[src] = S3 => (mr <= round'[src])
                               /\ step'[src] /= S3 => (mr < round'[src])
        BY DEF Lemma4_MessagesNotFromFuture
  <1>P1. \A m \in msgs1'[r] : m.src \in CORRECT =>
            /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
            /\ step'[m.src] = S1 => (m.r < round'[m.src])
    <2> SUFFICES ASSUME NEW m \in msgs1'[r], m.src \in CORRECT
                 PROVE /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                       /\ step'[m.src] = S1 => (m.r < round'[m.src]) OBVIOUS
    <2>0. m \in msgs1[r] BY <1>upd
    <2>nat. m.r \in Nat BY <2>0, Msgs1Shape, RoundsNat
    <2>a. CASE m.src = id
          <3>1. m.r <= round[id] BY <2>a, <2>0, <1>l4, <1>s3, <1>dist DEF Lemma4_MessagesNotFromFuture
          <3>2. step'[m.src] = S1 /\ round'[m.src] = round[id] + 1 BY <2>a, <1>st, <1>rd
          <3> QED BY <3>1, <3>2, <2>nat, <1>r0, <1>dist
    <2>b. CASE m.src # id
          <3>1. step'[m.src] = step[m.src] /\ round'[m.src] = round[m.src] BY <2>b, <1>st, <1>rd
          <3> QED BY <2>b, <2>0, <3>1, <1>l4 DEF Lemma4_MessagesNotFromFuture
    <2> QED BY <2>a, <2>b
  <1>P2. \A m \in msgs2'[r] :
            LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
            IN src \in CORRECT =>
                 /\ step'[src] = S3 => (mr <= round'[src])
                 /\ step'[src] /= S3 => (mr < round'[src])
    <2> SUFFICES ASSUME NEW m \in msgs2'[r],
                  (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) \in CORRECT
                 PROVE LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                           mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                       IN /\ step'[src] = S3 => (mr <= round'[src])
                          /\ step'[src] /= S3 => (mr < round'[src]) OBVIOUS
    <2> DEFINE src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
    <2>0. m \in msgs2[r] BY <1>upd
    <2>mr. (IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r) = r BY <2>0, Msgs2RShape, VariantAx
    <2>nat. (IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r) \in Nat BY <2>mr, RoundsNat
    <2>a. CASE src = id
          <3>1. (IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r) <= round[id]
                BY <2>a, <2>0, <1>l4, <1>s3, <1>dist DEF Lemma4_MessagesNotFromFuture
          <3>2. step'[src] = S1 /\ round'[src] = round[id] + 1 BY <2>a, <1>st, <1>rd
          <3> QED BY <3>1, <3>2, <2>nat, <1>r0, <1>dist
    <2>b. CASE src # id
          <3>1. step'[src] = step[src] /\ round'[src] = round[src] BY <2>b, <1>st, <1>rd
          <3> QED BY <2>b, <2>0, <3>1, <1>l4 DEF Lemma4_MessagesNotFromFuture
    <2> QED BY <2>a, <2>b
  <1> QED BY <1>P1, <1>P2
\* Substantive Step2 case: id sends a new D2(id,r,v) or Q2(id,r) into msgs2[r] and moves
\* S2->S3. The new message carries round r = round[id]; old bounds m.r < round become
\* m.r <= round (still ok). Handles Step2's two value-quorum branches uniformly via the
\* shared new-message round/sender shape.
THEOREM Pres_L4_S2 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma4_MessagesNotFromFuture'
  <1>l4. Lemma4_MessagesNotFromFuture BY DEF IndInv
  <1>r0. round[id] \in ROUNDS /\ round[id] \in Nat BY RoundsNat DEF TypeOK
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>dist. S1 # S2 /\ S2 # S3 /\ S1 # S3 BY DEF S1, S2, S3
  <1>fr. step' = [ step EXCEPT ![id] = S3 ] /\ msgs1' = msgs1 /\ round' = round BY DEF Step2
  <1>s2. step[id] = S2 BY DEF Step2
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id THEN S3 ELSE step[x]) BY <1>fr, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = round[x] BY <1>fr, <1>doms
  <1>nm. PICK nm :
            /\ msgs2' = [ msgs2 EXCEPT ![round[id]] = msgs2[round[id]] \union { nm } ]
            /\ (IF IsD2(nm) THEN AsD2(nm).src ELSE AsQ2(nm).src) = id
            /\ (IF IsD2(nm) THEN AsD2(nm).r ELSE AsQ2(nm).r) = round[id]
         BY VariantAx DEF Step2
  <1> SUFFICES ASSUME NEW r \in ROUNDS
               PROVE  /\ \A m \in msgs1'[r] : m.src \in CORRECT =>
                          /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                          /\ step'[m.src] = S1 => (m.r < round'[m.src])
                      /\ \A m \in msgs2'[r] :
                          LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                              mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                          IN src \in CORRECT =>
                               /\ step'[src] = S3 => (mr <= round'[src])
                               /\ step'[src] /= S3 => (mr < round'[src])
        BY DEF Lemma4_MessagesNotFromFuture
  <1>P1. \A m \in msgs1'[r] : m.src \in CORRECT =>
            /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
            /\ step'[m.src] = S1 => (m.r < round'[m.src])
    <2> SUFFICES ASSUME NEW m \in msgs1'[r], m.src \in CORRECT
                 PROVE /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                       /\ step'[m.src] = S1 => (m.r < round'[m.src]) OBVIOUS
    <2>0. m \in msgs1[r] BY <1>fr
    <2>a. CASE m.src = id
          <3>1. step'[m.src] = S3 /\ round'[m.src] = round[id] BY <2>a, <1>st, <1>rd
          <3>2. m.r <= round[id] BY <2>a, <2>0, <1>l4, <1>s2, <1>dist DEF Lemma4_MessagesNotFromFuture
          <3> QED BY <3>1, <3>2, <1>dist
    <2>b. CASE m.src # id
          <3>1. step'[m.src] = step[m.src] /\ round'[m.src] = round[m.src] BY <2>b, <1>st, <1>rd
          <3> QED BY <2>b, <2>0, <3>1, <1>l4 DEF Lemma4_MessagesNotFromFuture
    <2> QED BY <2>a, <2>b
  <1>P2. \A m \in msgs2'[r] :
            LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
            IN src \in CORRECT =>
                 /\ step'[src] = S3 => (mr <= round'[src])
                 /\ step'[src] /= S3 => (mr < round'[src])
    <2> SUFFICES ASSUME NEW m \in msgs2'[r],
                  (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) \in CORRECT
                 PROVE LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                           mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                       IN /\ step'[src] = S3 => (mr <= round'[src])
                          /\ step'[src] /= S3 => (mr < round'[src]) OBVIOUS
    <2> DEFINE src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
    <2> DEFINE mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
    <2>0. m \in msgs2[r] \/ (r = round[id] /\ m = nm) BY <1>nm, <1>dom2, <1>r0
    <2>old. CASE m \in msgs2[r]
          <3>nat. mr = r BY <2>old, Msgs2RShape, VariantAx
          <3>natN. mr \in Nat BY <3>nat, RoundsNat
          <3>a. CASE src = id
                <4>1. mr < round[id] BY <2>old, <3>a, <1>l4, <1>s2, <1>dist DEF Lemma4_MessagesNotFromFuture
                <4>2. step'[src] = S3 /\ round'[src] = round[id] BY <3>a, <1>st, <1>rd
                <4> QED BY <4>1, <4>2, <3>natN, <1>r0, <1>dist
          <3>b. CASE src # id
                <4>1. step'[src] = step[src] /\ round'[src] = round[src] BY <3>b, <1>st, <1>rd
                <4> QED BY <2>old, <3>b, <4>1, <1>l4 DEF Lemma4_MessagesNotFromFuture
          <3> QED BY <3>a, <3>b
    <2>nw. CASE r = round[id] /\ m = nm
          <3>1. src = id /\ mr = round[id] BY <2>nw, <1>nm
          <3>2. step'[src] = S3 /\ round'[src] = round[id] BY <3>1, <1>st, <1>rd
          <3> QED BY <3>1, <3>2, <1>r0, <1>dist
    <2> QED BY <2>0, <2>old, <2>nw
  <1> QED BY <1>P1, <1>P2
\* FaultyStep case: step/round unchanged and messages only grow with FAULTY-sender
\* messages, so any CORRECT-sender message is old and satisfies the (unchanged) bound.
THEOREM Pres_L4_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma4_MessagesNotFromFuture'
  <1>l4. Lemma4_MessagesNotFromFuture BY DEF IndInv
  <1>p. /\ step' = step /\ round' = round
        /\ \A rr \in ROUNDS : \A m \in msgs1'[rr] : m \notin msgs1[rr] => m.src \in FAULTY
        /\ \A rr \in ROUNDS : \A m \in msgs2'[rr] :
              m \notin msgs2[rr] =>
                ((IsD2(m) => AsD2(m).src \in FAULTY) /\ (IsQ2(m) => AsQ2(m).src \in FAULTY))
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW r \in ROUNDS
        PROVE /\ \A m \in msgs1'[r] : m.src \in CORRECT =>
                  /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                  /\ step'[m.src] = S1 => (m.r < round'[m.src])
              /\ \A m \in msgs2'[r] :
                  LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                      mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                  IN src \in CORRECT =>
                       /\ step'[src] = S3 => (mr <= round'[src])
                       /\ step'[src] /= S3 => (mr < round'[src])
        BY DEF Lemma4_MessagesNotFromFuture
  <1>P1. \A m \in msgs1'[r] : m.src \in CORRECT =>
            /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
            /\ step'[m.src] = S1 => (m.r < round'[m.src])
    <2> SUFFICES ASSUME NEW m \in msgs1'[r], m.src \in CORRECT PROVE
                   /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                   /\ step'[m.src] = S1 => (m.r < round'[m.src]) OBVIOUS
    <2>1. m \in msgs1[r] BY <1>p, DisjointCF
    <2> QED BY <2>1, <1>l4, <1>p DEF Lemma4_MessagesNotFromFuture
  <1>P2. \A m \in msgs2'[r] :
            LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
            IN src \in CORRECT =>
                 /\ step'[src] = S3 => (mr <= round'[src])
                 /\ step'[src] /= S3 => (mr < round'[src])
    <2> SUFFICES ASSUME NEW m \in msgs2'[r],
                  (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) \in CORRECT
                 PROVE LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                           mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                       IN /\ step'[src] = S3 => (mr <= round'[src])
                          /\ step'[src] /= S3 => (mr < round'[src]) OBVIOUS
    <2>1. m \in msgs2[r] BY <1>p, DisjointCF, VariantAx
    <2> QED BY <2>1, <1>l4, <1>p DEF Lemma4_MessagesNotFromFuture
  <1> QED BY <1>P1, <1>P2
THEOREM Pres_Lemma4 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma4_MessagesNotFromFuture'
  <1> QED BY Pres_L4_S1, Pres_L4_S2, Pres_L4_S3, Pres_L4_ST, Pres_L4_F DEF Next, CorrectStep

\* ===== L5: a non-initial round requires previously sent messages =====
THEOREM Pres_L5_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma5_RoundNeedsSentMessages'
  BY DEF IndInv, Lemma5_RoundNeedsSentMessages, vars
\* Substantive Step1 case: id sends its first M1 of round[id] and moves S1->S2. The new
\* M1 witnesses the now-active "r = round[id] /\ step /= S1" obligation; all other
\* obligations are preserved because msgs1 only grows (monotonicity) and msgs2 is unchanged.
THEOREM Pres_L5_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma5_RoundNeedsSentMessages'
  <1>l5. Lemma5_RoundNeedsSentMessages BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom1. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dist. S1 # S2 /\ S2 # S3 /\ S1 # S3 BY DEF S1, S2, S3
  <1>upd. /\ msgs1' = [ msgs1 EXCEPT
                ![round[id0]] = msgs1[round[id0]] \union { M1(id0, round[id0], value[id0]) } ]
          /\ step' = [ step EXCEPT ![id0] = S2 ] /\ round' = round /\ msgs2' = msgs2
          BY DEF Step1
  <1>mono. \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr] BY <1>upd, <1>dom1, <1>r0
  <1>new. M1(id0, round[id0], value[id0]).src = id0
          /\ M1(id0, round[id0], value[id0]) \in msgs1'[round[id0]]
          BY <1>upd, <1>dom1, <1>r0 DEF M1
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id0 THEN S2 ELSE step[x]) BY <1>upd, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = round[x] BY <1>upd, <1>doms
  <1> SUFFICES ASSUME NEW id \in CORRECT, NEW r \in ROUNDS
        PROVE /\ (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
              /\ (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
              /\ (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
        BY DEF Lemma5_RoundNeedsSentMessages
  <1>old. /\ (r < round[id] \/ (r = round[id] /\ step[id] /= S1)) => (\E m \in msgs1[r]: m.src = id)
          /\ (r < round[id]) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          /\ (r = round[id] /\ step[id] = S3) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          BY <1>l5 DEF Lemma5_RoundNeedsSentMessages
  <1>rid. round'[id] = round[id] BY <1>rd
  <1>c1. (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
    <2> SUFFICES ASSUME r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)
                 PROVE  \E m \in msgs1'[r]: m.src = id OBVIOUS
    <2>1. CASE id = id0 /\ r = round[id0] BY <2>1, <1>new
    <2>2. CASE ~(id = id0 /\ r = round[id0])
          <3>1. r < round[id] \/ (r = round[id] /\ step[id] /= S1) BY <2>2, <1>rid, <1>st, <1>dist
          <3>2. \E m \in msgs1[r] : m.src = id BY <3>1, <1>old
          <3> QED BY <3>2, <1>mono
    <2> QED BY <2>1, <2>2
  <1>c2. (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
         BY <1>old, <1>upd, <1>rid
  <1>c3. (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
    <2> SUFFICES ASSUME r = round'[id], step'[id] = S3
                 PROVE  \E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id OBVIOUS
    <2>1. step[id] = S3 BY <1>st, <1>dist
    <2> QED BY <2>1, <1>rid, <1>old, <1>upd
  <1> QED BY <1>c1, <1>c2, <1>c3
\* Step2 case: id sends a new type-2 message into msgs2[round[id]] (witnessing the
\* "r = round[id] /\ step = S3" obligation) and moves S2->S3; msgs1 unchanged, msgs2 grows.
THEOREM Pres_L5_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma5_RoundNeedsSentMessages'
  <1>l5. Lemma5_RoundNeedsSentMessages BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dist. S1 # S2 /\ S2 # S3 /\ S1 # S3 BY DEF S1, S2, S3
  <1>fr. step' = [ step EXCEPT ![id0] = S3 ] /\ msgs1' = msgs1 /\ round' = round BY DEF Step2
  <1>s2. step[id0] = S2 BY DEF Step2
  <1>nm. PICK nm :
            /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] = msgs2[round[id0]] \union { nm } ]
            /\ (IF IsD2(nm) THEN AsD2(nm).src ELSE AsQ2(nm).src) = id0 BY VariantAx DEF Step2
  <1>mono. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr] BY <1>nm, <1>dom2, <1>r0
  <1>nmsrc. AsD2(nm).src = id0 \/ AsQ2(nm).src = id0
    <2>1. CASE IsD2(nm) BY <2>1, <1>nm
    <2>2. CASE ~ IsD2(nm) BY <2>2, <1>nm
    <2> QED BY <2>1, <2>2
  <1>nmin. nm \in msgs2'[round[id0]]
    <2>1. msgs2'[round[id0]] = msgs2[round[id0]] \union { nm } BY <1>nm, <1>dom2, <1>r0
    <2> QED BY <2>1
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id0 THEN S3 ELSE step[x]) BY <1>fr, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = round[x] BY <1>fr, <1>doms
  <1> SUFFICES ASSUME NEW id \in CORRECT, NEW r \in ROUNDS
        PROVE /\ (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
              /\ (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
              /\ (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
        BY DEF Lemma5_RoundNeedsSentMessages
  <1>old. /\ (r < round[id] \/ (r = round[id] /\ step[id] /= S1)) => (\E m \in msgs1[r]: m.src = id)
          /\ (r < round[id]) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          /\ (r = round[id] /\ step[id] = S3) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          BY <1>l5 DEF Lemma5_RoundNeedsSentMessages
  <1>rid. round'[id] = round[id] BY <1>rd
  <1>c1. (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
    <2> SUFFICES ASSUME r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)
                 PROVE  \E m \in msgs1[r]: m.src = id BY <1>fr
    <2>1. r < round[id] \/ (r = round[id] /\ step[id] /= S1) BY <1>rid, <1>st, <1>dist, <1>s2
    <2> QED BY <2>1, <1>old
  <1>c2. (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
    <2> SUFFICES ASSUME r < round'[id] PROVE \E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id OBVIOUS
    <2>1. \E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id BY <1>rid, <1>old
    <2> QED BY <2>1, <1>mono
  <1>c3. (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
    <2> SUFFICES ASSUME r = round'[id], step'[id] = S3
                 PROVE  \E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id OBVIOUS
    <2>1. CASE id = id0 BY <2>1, <1>rid, <1>nmsrc, <1>nmin
    <2>2. CASE id # id0
          <3>1. r = round[id] /\ step[id] = S3 BY <2>2, <1>rid, <1>st
          <3>2. \E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id BY <3>1, <1>old
          <3> QED BY <3>2, <1>mono
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>c1, <1>c2, <1>c3
\* Step3 case: id advances round and resets step to S1; messages unchanged. The "step=S3"
\* obligations at round[id] become "r < round[id]+1" obligations, served by the same messages.
THEOREM Pres_L5_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma5_RoundNeedsSentMessages'
  <1>l5. Lemma5_RoundNeedsSentMessages BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS /\ round[id0] \in Nat BY RoundsNat DEF TypeOK
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dist. S1 # S2 /\ S2 # S3 /\ S1 # S3 BY DEF S1, S2, S3
  <1>upd. /\ round' = [ round EXCEPT ![id0] = round[id0] + 1 ] /\ step' = [ step EXCEPT ![id0] = S1 ]
          /\ msgs1' = msgs1 /\ msgs2' = msgs2 BY DEF Step3
  <1>s3. step[id0] = S3 BY DEF Step3
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id0 THEN S1 ELSE step[x]) BY <1>upd, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = (IF x = id0 THEN round[id0] + 1 ELSE round[x]) BY <1>upd, <1>doms
  <1> SUFFICES ASSUME NEW id \in CORRECT, NEW r \in ROUNDS
        PROVE /\ (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
              /\ (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
              /\ (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
        BY DEF Lemma5_RoundNeedsSentMessages
  <1>old. /\ (r < round[id] \/ (r = round[id] /\ step[id] /= S1)) => (\E m \in msgs1[r]: m.src = id)
          /\ (r < round[id]) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          /\ (r = round[id] /\ step[id] = S3) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          BY <1>l5 DEF Lemma5_RoundNeedsSentMessages
  <1>rN. r \in Nat BY RoundsNat
  <1>c1. (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
    <2> SUFFICES ASSUME r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)
                 PROVE  \E m \in msgs1[r]: m.src = id BY <1>upd
    <2>1. CASE id = id0
          <3>1. r < round[id] \/ (r = round[id] /\ step[id] /= S1)
                BY <2>1, <1>rd, <1>st, <1>rN, <1>r0, <1>s3, <1>dist
          <3> QED BY <3>1, <1>old
    <2>2. CASE id # id0
          <3>1. r < round[id] \/ (r = round[id] /\ step[id] /= S1) BY <2>2, <1>rd, <1>st
          <3> QED BY <3>1, <1>old
    <2> QED BY <2>1, <2>2
  <1>c2. (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
    <2> SUFFICES ASSUME r < round'[id] PROVE \E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id BY <1>upd
    <2>1. CASE id = id0
          <3>1. r < round[id] \/ (r = round[id] /\ step[id] = S3) BY <2>1, <1>rd, <1>rN, <1>r0, <1>s3
          <3> QED BY <3>1, <1>old
    <2>2. CASE id # id0
          <3>1. r < round[id] BY <2>2, <1>rd
          <3> QED BY <3>1, <1>old
    <2> QED BY <2>1, <2>2
  <1>c3. (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
    <2> SUFFICES ASSUME r = round'[id], step'[id] = S3
                 PROVE  \E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id BY <1>upd
    <2>1. id # id0 BY <1>st, <1>dist
    <2>2. r = round[id] /\ step[id] = S3 BY <2>1, <1>rd, <1>st
    <2> QED BY <2>2, <1>old
  <1> QED BY <1>c1, <1>c2, <1>c3
\* FaultyStep case: step/round unchanged, messages only grow, so every required message
\* (a CORRECT replica's own message) still exists.
THEOREM Pres_L5_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma5_RoundNeedsSentMessages'
  <1>l5. Lemma5_RoundNeedsSentMessages BY DEF IndInv
  <1>p. /\ step' = step /\ round' = round
        /\ \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr] /\ msgs2[rr] \subseteq msgs2'[rr]
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW id \in CORRECT, NEW r \in ROUNDS
        PROVE /\ (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
              /\ (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
              /\ (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
        BY DEF Lemma5_RoundNeedsSentMessages
  <1>old. /\ (r < round[id] \/ (r = round[id] /\ step[id] /= S1)) => (\E m \in msgs1[r]: m.src = id)
          /\ (r < round[id]) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          /\ (r = round[id] /\ step[id] = S3) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          BY <1>l5 DEF Lemma5_RoundNeedsSentMessages
  <1> QED BY <1>old, <1>p
THEOREM Pres_Lemma5 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma5_RoundNeedsSentMessages'
  <1> QED BY Pres_L5_S1, Pres_L5_S2, Pres_L5_S3, Pres_L5_ST, Pres_L5_F DEF Next, CorrectStep

\* ===== L6: a decision fixes the value (decision,value) =====
THEOREM Pres_L6_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma6_DecisionDefinesValue'
  BY DEF IndInv, Lemma6_DecisionDefinesValue, Step1
THEOREM Pres_L6_S2 ==
  ASSUME IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma6_DecisionDefinesValue'
  BY DEF IndInv, Lemma6_DecisionDefinesValue, Step2
\* FaultyStep leaves value/decision unchanged (frame), via FaultyStepProps.
THEOREM Pres_L6_F ==
  ASSUME IndInv, FaultyStep
  PROVE  Lemma6_DecisionDefinesValue'
  <1>1. value' = value /\ decision' = decision BY FaultyStepProps
  <1> QED BY <1>1 DEF IndInv, Lemma6_DecisionDefinesValue
THEOREM Pres_L6_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma6_DecisionDefinesValue'
  BY DEF IndInv, Lemma6_DecisionDefinesValue, vars
THEOREM Pres_Lemma6 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma6_DecisionDefinesValue'
  <1>o1. ASSUME NEW id \in CORRECT, Step3(id) PROVE Lemma6_DecisionDefinesValue'
        OMITTED \* TODO: substantive Step3 case for Lemma6_DecisionDefinesValue
  <1> QED BY Pres_L6_S1, Pres_L6_S2, Pres_L6_F, Pres_L6_ST, <1>o1 DEF Next, CorrectStep

\* ===== L7: a correct D2(v) requires a type-1 quorum for v =====
THEOREM Pres_L7_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma7_D2RequiresQuorum'
  BY DEF IndInv, Lemma7_D2RequiresQuorum, Step3
THEOREM Pres_L7_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma7_D2RequiresQuorum'
  <1>l7. Lemma7_D2RequiresQuorum BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom1. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>upd. /\ msgs1' = [ msgs1 EXCEPT
                ![round[id0]] = msgs1[round[id0]] \union { M1(id0, round[id0], value[id0]) } ]
          /\ msgs2' = msgs2
          BY DEF Step1
  <1>grow. \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr]
        BY <1>upd, <1>dom1, <1>r0
  <1> SUFFICES ASSUME NEW r \in ROUNDS, NEW v \in VALUES,
                      \E m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in CORRECT
               PROVE  LET ExistsQuorum1(rr, vv) ==
                         LET Sv == { m \in msgs1'[rr]: m.v = vv } IN
                         2 * Cardinality(Senders1(Sv)) > N + T
                      IN ExistsQuorum1(r, v)
        BY DEF Lemma7_D2RequiresQuorum
  <1>old. LET ExistsQuorum1(rr, vv) ==
             LET Sv == { m \in msgs1[rr]: m.v = vv } IN
             2 * Cardinality(Senders1(Sv)) > N + T
          IN ExistsQuorum1(r, v)
        BY <1>l7, <1>upd DEF Lemma7_D2RequiresQuorum
  <1>sub. { m \in msgs1[r] : m.v = v } \subseteq { m \in msgs1'[r] : m.v = v }
        BY <1>grow
  <1>mono. Cardinality(Senders1({ m \in msgs1[r] : m.v = v }))
              <= Cardinality(Senders1({ m \in msgs1'[r] : m.v = v }))
        BY <1>sub, Senders1_Mono
  <1>types. Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) \in Nat
             /\ Cardinality(Senders1({ m \in msgs1'[r] : m.v = v })) \in Nat
             /\ N + T \in Nat
        BY Senders1_Sub, FS_CardinalityType, ConstNat
  <1> QED BY <1>old, <1>mono, <1>types, Arith_DoubleGtMono
THEOREM Pres_L7_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma7_D2RequiresQuorum'
  <1>l7. Lemma7_D2RequiresQuorum BY DEF IndInv
  <1>p. /\ \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr]
        /\ \A rr \in ROUNDS : \A m \in msgs2'[rr] :
              m \notin msgs2[rr] =>
                ((IsD2(m) => AsD2(m).src \in FAULTY) /\ (IsQ2(m) => AsQ2(m).src \in FAULTY))
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW r \in ROUNDS, NEW v \in VALUES,
                      \E m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in CORRECT
               PROVE  LET ExistsQuorum1(rr, vv) ==
                         LET Sv == { m \in msgs1'[rr]: m.v = vv } IN
                         2 * Cardinality(Senders1(Sv)) > N + T
                      IN ExistsQuorum1(r, v)
        BY DEF Lemma7_D2RequiresQuorum
  <1> PICK md \in msgs2'[r] : IsD2(md) /\ AsD2(md).v = v /\ AsD2(md).src \in CORRECT
        OBVIOUS
  <1>oldD2. md \in msgs2[r] BY <1>p, DisjointCF
  <1>old. LET ExistsQuorum1(rr, vv) ==
             LET Sv == { m \in msgs1[rr]: m.v = vv } IN
             2 * Cardinality(Senders1(Sv)) > N + T
          IN ExistsQuorum1(r, v)
        BY <1>l7, <1>oldD2 DEF Lemma7_D2RequiresQuorum
  <1>sub. { m \in msgs1[r] : m.v = v } \subseteq { m \in msgs1'[r] : m.v = v }
        BY <1>p
  <1>mono. Cardinality(Senders1({ m \in msgs1[r] : m.v = v }))
              <= Cardinality(Senders1({ m \in msgs1'[r] : m.v = v }))
        BY <1>sub, Senders1_Mono
  <1>types. Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) \in Nat
             /\ Cardinality(Senders1({ m \in msgs1'[r] : m.v = v })) \in Nat
             /\ N + T \in Nat
        BY Senders1_Sub, FS_CardinalityType, ConstNat
  <1> QED BY <1>old, <1>mono, <1>types, Arith_DoubleGtMono
THEOREM Pres_L7_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma7_D2RequiresQuorum'
  <1>l7. Lemma7_D2RequiresQuorum BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>m1same. msgs1' = msgs1 BY DEF Step2
  <1> PICK received \in SUBSET msgs1[round[id0]] :
        /\ Cardinality(Senders1(received)) >= N - T
        /\ LET Weights == [ vv \in VALUES |->
             Cardinality(Senders1({ m \in received : m.v = vv })) ]
           IN
           \/ \E vv \in VALUES:
                /\ 2 * Weights[vv] > N + T
                /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                    msgs2[round[id0]] \union { D2(id0, round[id0], vv) } ]
           \/ /\ \A vv \in VALUES: 2 * Weights[vv] <= N + T
              /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                    msgs2[round[id0]] \union { Q2(id0, round[id0]) } ]
        BY DEF Step2
  <1> DEFINE Weights == [ vv \in VALUES |->
             Cardinality(Senders1({ m \in received : m.v = vv })) ]
  <1> SUFFICES ASSUME NEW r \in ROUNDS, NEW v \in VALUES,
                      \E m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in CORRECT
               PROVE  LET ExistsQuorum1(rr, vv) ==
                         LET Sv == { m \in msgs1'[rr]: m.v = vv } IN
                         2 * Cardinality(Senders1(Sv)) > N + T
                      IN ExistsQuorum1(r, v)
        BY DEF Lemma7_D2RequiresQuorum
  <1> PICK md \in msgs2'[r] : IsD2(md) /\ AsD2(md).v = v /\ AsD2(md).src \in CORRECT
        OBVIOUS
  <1>oldMsg. CASE md \in msgs2[r]
    <2>old. LET ExistsQuorum1(rr, vv) ==
               LET Sv == { m \in msgs1[rr]: m.v = vv } IN
               2 * Cardinality(Senders1(Sv)) > N + T
            IN ExistsQuorum1(r, v)
          BY <1>l7, <1>oldMsg DEF Lemma7_D2RequiresQuorum
    <2> QED BY <2>old, <1>m1same
  <1>newMsg. CASE md \notin msgs2[r]
    <2>d. CASE \E vv \in VALUES:
              /\ 2 * Weights[vv] > N + T
              /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                    msgs2[round[id0]] \union { D2(id0, round[id0], vv) } ]
      <3> PICK vd \in VALUES:
            /\ 2 * Weights[vd] > N + T
            /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                  msgs2[round[id0]] \union { D2(id0, round[id0], vd) } ]
          BY <2>d
      <3>eq. r = round[id0] /\ md = D2(id0, round[id0], vd)
          BY <1>newMsg, <1>dom2, <1>r0
      <3>veq. v = vd BY <3>eq, VariantAx
      <3>sub. { m \in received : m.v = vd } \subseteq { m \in msgs1[round[id0]] : m.v = vd }
          OBVIOUS
      <3>mono. Cardinality(Senders1({ m \in received : m.v = vd }))
                  <= Cardinality(Senders1({ m \in msgs1[round[id0]] : m.v = vd }))
          BY <3>sub, Senders1_Mono
      <3>types. Cardinality(Senders1({ m \in received : m.v = vd })) \in Nat
                 /\ Cardinality(Senders1({ m \in msgs1[round[id0]] : m.v = vd })) \in Nat
                 /\ N + T \in Nat
          BY Senders1_Sub, FS_CardinalityType, ConstNat
      <3>gt. 2 * Cardinality(Senders1({ m \in received : m.v = vd })) > N + T
          BY <2>d DEF Weights
      <3> QED BY <3>eq, <3>veq, <3>gt, <3>mono, <3>types, <1>m1same, Arith_DoubleGtMono
    <2>q. CASE /\ \A vv \in VALUES: 2 * Weights[vv] <= N + T
                /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                      msgs2[round[id0]] \union { Q2(id0, round[id0]) } ]
      <3>eq. r = round[id0] /\ md = Q2(id0, round[id0])
          BY <2>q, <1>newMsg, <1>dom2, <1>r0
      <3> QED BY <3>eq, VariantAx
    <2> QED BY <2>d, <2>q
  <1> QED BY <1>oldMsg, <1>newMsg
THEOREM Pres_L7_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma7_D2RequiresQuorum'
  BY DEF IndInv, Lemma7_D2RequiresQuorum, vars
THEOREM Pres_Lemma7 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma7_D2RequiresQuorum'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step1(id) => Lemma7_D2RequiresQuorum'
    <2> SUFFICES ASSUME Step1(id) PROVE Lemma7_D2RequiresQuorum'
          OBVIOUS
    <2> QED BY Pres_L7_S1
  <1>o2. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma7_D2RequiresQuorum'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma7_D2RequiresQuorum'
          OBVIOUS
    <2> QED BY Pres_L7_S2
  <1>o3. FaultyStep => Lemma7_D2RequiresQuorum'
    <2> SUFFICES ASSUME FaultyStep PROVE Lemma7_D2RequiresQuorum'
          OBVIOUS
    <2> QED BY Pres_L7_F
  <1> QED BY Pres_L7_S3, Pres_L7_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep

\* ===== L8: a correct Q2 means no type-1 quorum existed =====
THEOREM Pres_L8_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
  BY DEF IndInv, Lemma8_Q2RequiresNoQuorumFaster, Step3
THEOREM Pres_L8_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
  BY DEF IndInv, Lemma8_Q2RequiresNoQuorumFaster, vars
THEOREM Pres_Lemma8 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
  <1>o1. ASSUME NEW id \in CORRECT, Step1(id) PROVE Lemma8_Q2RequiresNoQuorumFaster'
        OMITTED \* TODO: substantive Step1 case for Lemma8_Q2RequiresNoQuorumFaster
  <1>o2. ASSUME NEW id \in CORRECT, Step2(id) PROVE Lemma8_Q2RequiresNoQuorumFaster'
        OMITTED \* TODO: substantive Step2 case for Lemma8_Q2RequiresNoQuorumFaster
  <1>o3. ASSUME FaultyStep PROVE Lemma8_Q2RequiresNoQuorumFaster'
        OMITTED \* TODO: substantive FaultyStep case for Lemma8_Q2RequiresNoQuorumFaster
  <1> QED BY Pres_L8_S3, Pres_L8_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep

\* ===== L9: rounds connection / value support carries forward =====
THEOREM Pres_L9_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma9_RoundsConnection'
  BY DEF IndInv, Lemma9_RoundsConnection, SupportedValues, Step3
THEOREM Pres_L9_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma9_RoundsConnection'
  BY DEF IndInv, Lemma9_RoundsConnection, SupportedValues, vars
THEOREM Pres_Lemma9 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma9_RoundsConnection'
  <1>o1. ASSUME NEW id \in CORRECT, Step1(id) PROVE Lemma9_RoundsConnection'
        OMITTED \* TODO: substantive Step1 case for Lemma9_RoundsConnection
  <1>o2. ASSUME NEW id \in CORRECT, Step2(id) PROVE Lemma9_RoundsConnection'
        OMITTED \* TODO: substantive Step2 case for Lemma9_RoundsConnection
  <1>o3. ASSUME FaultyStep PROVE Lemma9_RoundsConnection'
        OMITTED \* TODO: substantive FaultyStep case for Lemma9_RoundsConnection
  <1> QED BY Pres_L9_S3, Pres_L9_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep

\* ===== L10: a type-1 message in round r>1 needs a quorum in r-1 =====
THEOREM Pres_L10_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma10_M1RequiresQuorum'
  BY DEF IndInv, Lemma10_M1RequiresQuorum, Step3
THEOREM Pres_L10_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma10_M1RequiresQuorum'
  <1>l10. Lemma10_M1RequiresQuorum BY DEF IndInv
  <1>l12. Lemma12_CannotJumpRoundsWithoutQuorum BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom1. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>upd. /\ msgs1' = [ msgs1 EXCEPT
                ![round[id0]] = msgs1[round[id0]] \union { M1(id0, round[id0], value[id0]) } ]
          /\ msgs2' = msgs2
          BY DEF Step1
  <1>s1. step[id0] = S1 BY DEF Step1
  <1> SUFFICES ASSUME NEW r \in { rr \in ROUNDS \ { 1 } :
                                  \E m \in msgs1'[rr] : m.src \in CORRECT }
        PROVE Cardinality(Senders2(msgs2'[r - 1])) >= N - T
        BY DEF Lemma10_M1RequiresQuorum
  <1>rin. r \in ROUNDS /\ r # 1 /\ \E m \in msgs1'[r] : m.src \in CORRECT
        OBVIOUS
  <1> PICK m \in msgs1'[r] : m.src \in CORRECT BY <1>rin
  <1>split. m \in msgs1[r]
              \/ (r = round[id0] /\ m = M1(id0, round[id0], value[id0]))
        BY <1>upd, <1>dom1, <1>r0
  <1>old. CASE m \in msgs1[r]
    <2>rinOld. r \in ROUNDS \ { 1 } /\ \E mm \in msgs1[r] : mm.src \in CORRECT
          BY <1>old, <1>rin
    <2>q. Cardinality(Senders2(msgs2[r - 1])) >= N - T
          BY <1>l10, <2>rinOld DEF Lemma10_M1RequiresQuorum
    <2> QED BY <2>q, <1>upd
  <1>new. CASE r = round[id0] /\ m = M1(id0, round[id0], value[id0])
    <2>pred. r - 1 \in ROUNDS BY <1>rin, RoundPredInRounds
    <2>next. (r - 1) + 1 \in ROUNDS
              /\ \E id \in CORRECT : round[id] = (r - 1) + 1 /\ step[id] = S1
          BY <1>new, <1>r0, <1>s1, ConstNat, RoundsNat
    <2>q. Cardinality(Senders2(msgs2[r - 1])) >= N - T
          BY <1>l12, <2>pred, <2>next DEF Lemma12_CannotJumpRoundsWithoutQuorum
    <2> QED BY <2>q, <1>upd
  <1> QED BY <1>split, <1>old, <1>new
THEOREM Pres_L10_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma10_M1RequiresQuorum'
  <1>l10. Lemma10_M1RequiresQuorum BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>m1same. msgs1' = msgs1 BY DEF Step2
  <1>nm. PICK nm :
        msgs2' = [ msgs2 EXCEPT ![round[id0]] = msgs2[round[id0]] \union { nm } ]
      BY VariantAx DEF Step2
  <1>grow. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE msgs2[rr] \subseteq msgs2'[rr] OBVIOUS
    <2>eq. CASE rr = round[id0]
      <3> QED BY <2>eq, <1>nm, <1>r0, <1>dom2
    <2>ne. CASE rr # round[id0]
      <3> QED BY <2>ne, <1>nm, <1>r0, <1>dom2
    <2> QED BY <2>eq, <2>ne
  <1> SUFFICES ASSUME NEW r \in { rr \in ROUNDS \ { 1 } :
                                  \E m \in msgs1'[rr] : m.src \in CORRECT }
        PROVE Cardinality(Senders2(msgs2'[r - 1])) >= N - T
        BY DEF Lemma10_M1RequiresQuorum
  <1>rin. r \in ROUNDS /\ r # 1 /\ \E m \in msgs1[r] : m.src \in CORRECT
        BY <1>m1same
  <1>old. Cardinality(Senders2(msgs2[r - 1])) >= N - T
        BY <1>l10, <1>rin DEF Lemma10_M1RequiresQuorum
  <1>pred. r - 1 \in ROUNDS BY <1>rin, RoundPredInRounds
  <1>sub. msgs2[r - 1] \subseteq msgs2'[r - 1] BY <1>grow, <1>pred
  <1>mono. Cardinality(Senders2(msgs2[r - 1])) <= Cardinality(Senders2(msgs2'[r - 1]))
        BY <1>sub, Senders2_Mono
  <1>types. Cardinality(Senders2(msgs2[r - 1])) \in Nat
             /\ Cardinality(Senders2(msgs2'[r - 1])) \in Nat
             /\ N - T \in Nat
        BY Senders2_Sub, FS_CardinalityType, NgtT, ConstNat, FleqT
  <1> QED BY <1>old, <1>mono, <1>types, Arith_GeTrans
THEOREM Pres_L10_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma10_M1RequiresQuorum'
  <1>l10. Lemma10_M1RequiresQuorum BY DEF IndInv
  <1>p. /\ \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr]
        /\ \A rr \in ROUNDS : \A m \in msgs1'[rr] : m \notin msgs1[rr] => m.src \in FAULTY
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW r \in { rr \in ROUNDS \ { 1 } :
                                  \E m \in msgs1'[rr] : m.src \in CORRECT }
        PROVE Cardinality(Senders2(msgs2'[r - 1])) >= N - T
        BY DEF Lemma10_M1RequiresQuorum
  <1>rin. r \in ROUNDS /\ r # 1 /\ \E m \in msgs1'[r] : m.src \in CORRECT
        OBVIOUS
  <1> PICK m \in msgs1'[r] : m.src \in CORRECT BY <1>rin
  <1>oldMsg. m \in msgs1[r] BY <1>p, DisjointCF
  <1>old. Cardinality(Senders2(msgs2[r - 1])) >= N - T
        BY <1>l10, <1>rin, <1>oldMsg DEF Lemma10_M1RequiresQuorum
  <1>pred. r - 1 \in ROUNDS BY <1>rin, RoundPredInRounds
  <1>sub. msgs2[r - 1] \subseteq msgs2'[r - 1] BY <1>p, <1>pred
  <1>mono. Cardinality(Senders2(msgs2[r - 1])) <= Cardinality(Senders2(msgs2'[r - 1]))
        BY <1>sub, Senders2_Mono
  <1>types. Cardinality(Senders2(msgs2[r - 1])) \in Nat
             /\ Cardinality(Senders2(msgs2'[r - 1])) \in Nat
             /\ N - T \in Nat
        BY Senders2_Sub, FS_CardinalityType, NgtT, ConstNat, FleqT
  <1> QED BY <1>old, <1>mono, <1>types, Arith_GeTrans
THEOREM Pres_L10_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma10_M1RequiresQuorum'
  BY DEF IndInv, Lemma10_M1RequiresQuorum, vars
THEOREM Pres_Lemma10 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma10_M1RequiresQuorum'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step1(id) => Lemma10_M1RequiresQuorum'
    <2> SUFFICES ASSUME Step1(id) PROVE Lemma10_M1RequiresQuorum'
          OBVIOUS
    <2> QED BY Pres_L10_S1
  <1>o2. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma10_M1RequiresQuorum'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma10_M1RequiresQuorum'
          OBVIOUS
    <2> QED BY Pres_L10_S2
  <1>o3. FaultyStep => Lemma10_M1RequiresQuorum'
    <2> SUFFICES ASSUME FaultyStep PROVE Lemma10_M1RequiresQuorum'
          OBVIOUS
    <2> QED BY Pres_L10_F
  <1> QED BY Pres_L10_S3, Pres_L10_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep

\* ===== L11: a correct replica's value at r>1 is backed by msgs2[r-1] =====
THEOREM Pres_L11_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma11_ValueOnQuorumLessRam'
  BY DEF IndInv, Lemma11_ValueOnQuorumLessRam, Step1
THEOREM Pres_L11_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma11_ValueOnQuorumLessRam'
  BY DEF IndInv, Lemma11_ValueOnQuorumLessRam, vars
THEOREM Pres_Lemma11 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma11_ValueOnQuorumLessRam'
  <1>o1. ASSUME NEW id \in CORRECT, Step2(id) PROVE Lemma11_ValueOnQuorumLessRam'
        OMITTED \* TODO: substantive Step2 case for Lemma11_ValueOnQuorumLessRam
  <1>o2. ASSUME NEW id \in CORRECT, Step3(id) PROVE Lemma11_ValueOnQuorumLessRam'
        OMITTED \* TODO: substantive Step3 case for Lemma11_ValueOnQuorumLessRam
  <1>o3. ASSUME FaultyStep PROVE Lemma11_ValueOnQuorumLessRam'
        OMITTED \* TODO: substantive FaultyStep case for Lemma11_ValueOnQuorumLessRam
  <1> QED BY Pres_L11_S1, Pres_L11_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep

\* ===== L12: reaching round r+1 needs N-T type-2 messages in r =====
THEOREM Pres_L12_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
  <1>l12. Lemma12_CannotJumpRoundsWithoutQuorum BY DEF IndInv
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dist. S1 # S2 BY DEF S1, S2
  <1>upd. /\ step' = [ step EXCEPT ![id0] = S2 ]
          /\ round' = round
          /\ msgs2' = msgs2
          BY DEF Step1
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id0 THEN S2 ELSE step[x])
        BY <1>upd, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = round[x]
        BY <1>upd, <1>doms
  <1> SUFFICES ASSUME NEW r \in ROUNDS, r + 1 \in ROUNDS,
                      \E id \in CORRECT : round'[id] = r + 1 /\ step'[id] = S1
               PROVE  Cardinality(Senders2(msgs2'[r])) >= N - T
        BY DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1> PICK id \in CORRECT : round'[id] = r + 1 /\ step'[id] = S1
        OBVIOUS
  <1>notId0. id # id0 BY <1>st, <1>dist
  <1>oldNext. \E oldId \in CORRECT : round[oldId] = r + 1 /\ step[oldId] = S1
        BY <1>notId0, <1>st, <1>rd
  <1>old. Cardinality(Senders2(msgs2[r])) >= N - T
        BY <1>l12, <1>oldNext DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1> QED BY <1>old, <1>upd
THEOREM Pres_L12_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
  <1>l12. Lemma12_CannotJumpRoundsWithoutQuorum BY DEF IndInv
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dist. S1 # S3 BY DEF S1, S3
  <1>upd. /\ step' = [ step EXCEPT ![id0] = S3 ]
          /\ round' = round
          BY DEF Step2
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id0 THEN S3 ELSE step[x])
        BY <1>upd, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = round[x]
        BY <1>upd, <1>doms
  <1> SUFFICES ASSUME NEW r \in ROUNDS, r + 1 \in ROUNDS,
                      \E id \in CORRECT : round'[id] = r + 1 /\ step'[id] = S1
               PROVE  Cardinality(Senders2(msgs2'[r])) >= N - T
        BY DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1> PICK id \in CORRECT : round'[id] = r + 1 /\ step'[id] = S1
        OBVIOUS
  <1>notId0. id # id0 BY <1>st, <1>dist
  <1>oldNext. \E oldId \in CORRECT : round[oldId] = r + 1 /\ step[oldId] = S1
        BY <1>notId0, <1>st, <1>rd
  <1>old. Cardinality(Senders2(msgs2[r])) >= N - T
        BY <1>l12, <1>oldNext DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1>nm. PICK nm :
        msgs2' = [ msgs2 EXCEPT ![round[id0]] = msgs2[round[id0]] \union { nm } ]
        BY VariantAx DEF Step2
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>grow. msgs2[r] \subseteq msgs2'[r]
        BY <1>nm, <1>r0, <1>dom2
  <1>mono. Cardinality(Senders2(msgs2[r])) <= Cardinality(Senders2(msgs2'[r]))
        BY <1>grow, Senders2_Mono
  <1>types. Cardinality(Senders2(msgs2[r])) \in Nat
             /\ Cardinality(Senders2(msgs2'[r])) \in Nat
             /\ N - T \in Nat
        BY Senders2_Sub, FS_CardinalityType, NgtT, ConstNat, FleqT
  <1> QED BY <1>old, <1>mono, <1>types, Arith_GeTrans
THEOREM Pres_L12_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
  BY DEF IndInv, Lemma12_CannotJumpRoundsWithoutQuorum, vars
THEOREM Pres_Lemma12 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step1(id) => Lemma12_CannotJumpRoundsWithoutQuorum'
    <2> SUFFICES ASSUME Step1(id) PROVE Lemma12_CannotJumpRoundsWithoutQuorum'
          OBVIOUS
    <2> QED BY Pres_L12_S1
  <1>o2. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma12_CannotJumpRoundsWithoutQuorum'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma12_CannotJumpRoundsWithoutQuorum'
          OBVIOUS
    <2> QED BY Pres_L12_S2
  <1>o3. ASSUME NEW id \in CORRECT, Step3(id) PROVE Lemma12_CannotJumpRoundsWithoutQuorum'
        OMITTED \* TODO: substantive Step3 case for Lemma12_CannotJumpRoundsWithoutQuorum
  <1>o4. ASSUME FaultyStep PROVE Lemma12_CannotJumpRoundsWithoutQuorum'
        OMITTED \* TODO: substantive FaultyStep case for Lemma12_CannotJumpRoundsWithoutQuorum
  <1> QED BY Pres_L12_ST, <1>o1, <1>o2, <1>o3, <1>o4 DEF Next, CorrectStep

\* ===== L13: value lock -- a correct value at r matches Supported(r-1) =====
THEOREM Pres_L13_S1 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma13_ValueLock'
  BY RoundsNat DEF TypeOK, IndInv, Lemma13_ValueLock, SupportedValues, Step1
THEOREM Pres_L13_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma13_ValueLock'
  BY DEF IndInv, Lemma13_ValueLock, SupportedValues, vars
THEOREM Pres_Lemma13 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma13_ValueLock'
  <1>o1. ASSUME NEW id \in CORRECT, Step2(id) PROVE Lemma13_ValueLock'
        OMITTED \* TODO: substantive Step2 case for Lemma13_ValueLock
  <1>o2. ASSUME NEW id \in CORRECT, Step3(id) PROVE Lemma13_ValueLock'
        OMITTED \* TODO: substantive Step3 case for Lemma13_ValueLock
  <1>o3. ASSUME FaultyStep PROVE Lemma13_ValueLock'
        OMITTED \* TODO: substantive FaultyStep case for Lemma13_ValueLock
  <1> QED BY Pres_L13_S1, Pres_L13_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep

\* ===== L1: a decision is backed by a D2 quorum in the previous round =====
THEOREM Pres_L1_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
  BY DEF IndInv, Lemma1_DecisionRequiresLastQuorumLessRam, ExistsQuorum2LessRam, Step1
THEOREM Pres_L1_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
  BY DEF IndInv, Lemma1_DecisionRequiresLastQuorumLessRam, ExistsQuorum2LessRam, vars
THEOREM Pres_Lemma1 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
  <1>o1. ASSUME NEW id \in CORRECT, Step2(id) PROVE Lemma1_DecisionRequiresLastQuorumLessRam'
        OMITTED \* TODO: substantive Step2 case for Lemma1_DecisionRequiresLastQuorumLessRam
  <1>o2. ASSUME NEW id \in CORRECT, Step3(id) PROVE Lemma1_DecisionRequiresLastQuorumLessRam'
        OMITTED \* TODO: substantive Step3 case for Lemma1_DecisionRequiresLastQuorumLessRam
  <1>o3. ASSUME FaultyStep PROVE Lemma1_DecisionRequiresLastQuorumLessRam'
        OMITTED \* TODO: substantive FaultyStep case for Lemma1_DecisionRequiresLastQuorumLessRam
  <1> QED BY Pres_L1_S1, Pres_L1_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep
\* --- ASSEMBLED INDUCTIVE STEP ------------------------------------------------
THEOREM Inductive ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  TypeOK' /\ IndInv'
  BY TypePres, Pres_Lemma1, Pres_Lemma2, Pres_Lemma3, Pres_Lemma4, Pres_Lemma5,
     Pres_Lemma6, Pres_Lemma7, Pres_Lemma8, Pres_Lemma9, Pres_Lemma10,
     Pres_Lemma11, Pres_Lemma12, Pres_Lemma13
  DEF IndInv

\*****************************************************************************
\* SECTION D -- IndInv => AgreementInv (round induction)
\*****************************************************************************

\* SAME-ROUND UNIQUENESS: in one round, at most one value can hold a D2 quorum.
\* Proof idea: a D2(v) quorum (>half, >=T+1) implies (Lemma7) a type-1 quorum for v
\* with > (N+T)/2 senders. Two such type-1 quorums (for v and w) each exceed half of
\* N, so they intersect (QuorumIntersect) in a CORRECT replica, which then sent both
\* v and w in round r -- contradicting Lemma2 unless v = w.
THEOREM QuorumUnique ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES, NEW w \in VALUES,
         ExistsQuorum2LessRam(r, v), ExistsQuorum2LessRam(r, w)
  PROVE  v = w
  <1> USE DEF IndInv
  \* A D2(v) quorum of correct senders exists: of the >= T+1 D2(v) messages at most
  \* F are faulty (FaultyD2Bound), leaving a correct sender (CorrectD2Exists).
  <1>1. \E mv \in msgs2[r] : IsD2(mv) /\ AsD2(mv).v = v /\ AsD2(mv).src \in CORRECT
        <2>1. Cardinality(DvSet(r, v)) >= T + 1 BY DEF ExistsQuorum2LessRam, DvSet
        <2> QED BY <2>1, CorrectD2Exists
  <1>2. \E mw \in msgs2[r] : IsD2(mw) /\ AsD2(mw).v = w /\ AsD2(mw).src \in CORRECT
        <2>1. Cardinality(DvSet(r, w)) >= T + 1 BY DEF ExistsQuorum2LessRam, DvSet
        <2> QED BY <2>1, CorrectD2Exists
  <1>3. LET Sv == { m \in msgs1[r] : m.v = v }
            Sw == { m \in msgs1[r] : m.v = w }
        IN 2 * Cardinality(Senders1(Sv)) > N + T
           /\ 2 * Cardinality(Senders1(Sw)) > N + T
        BY <1>1, <1>2 DEF Lemma7_D2RequiresQuorum
  \* The two type-1 majorities (> (N+T)/2 each) meet in a correct sender (MajorityIntersect),
  \* which then sent both v and w in round r.
  <1>4. \E id \in CORRECT :
            (\E m \in msgs1[r] : m.src = id /\ m.v = v)
            /\ (\E m \in msgs1[r] : m.src = id /\ m.v = w)
        <2>1. Senders1({ m \in msgs1[r] : m.v = v }) \subseteq ALL
              /\ Senders1({ m \in msgs1[r] : m.v = w }) \subseteq ALL
              BY DEF Senders1
        <2>2. 2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) > N + T
              /\ 2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = w })) > N + T
              BY <1>3
        <2>3. \E id \in Senders1({ m \in msgs1[r] : m.v = v })
                    \cap Senders1({ m \in msgs1[r] : m.v = w }) : id \in CORRECT
              BY <2>1, <2>2, MajorityIntersect
        <2> QED BY <2>3 DEF Senders1
  <1> QED
        \* a correct id that sent both v and w in round r forces v = w by Lemma2
        BY <1>4 DEF Lemma2_NoEquivocation1ByCorrect

\* CROSS-ROUND LOCK: once value v has a D2 quorum at round a, every D2 quorum at any
\* round r >= a is also for v. By induction on r:
\*   base r = a: QuorumUnique;
\*   step r -> r+1: a quorum at r+1 for w needs (Lemma7) a type-1 quorum for w at r+1;
\*     by Lemma10/Lemma12 the round r+1 was entered from r with N-T type-2 messages, and
\*     by Lemma9/Lemma13 (value lock) every correct value entering round r+1 equals the
\*     value supported at r, which is v (carried from the round-r quorum). Hence w = v.
THEOREM LockLemma ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(a, v)
  PROVE  \A r \in ROUNDS :
            r >= a => (\A w \in VALUES : ExistsQuorum2LessRam(r, w) => w = v)
  <1> USE DEF IndInv
  \* Induction on the round offset k = r - a using NaturalsInduction.
  <1> a \in Nat
        BY RoundsNat
  <1> DEFINE P(k) == \A w \in VALUES :
                       (a + k) \in ROUNDS /\ ExistsQuorum2LessRam(a + k, w) => w = v
  <1>base. P(0)
        <2> SUFFICES ASSUME NEW w \in VALUES,
                            (a + 0) \in ROUNDS, ExistsQuorum2LessRam(a + 0, w)
                     PROVE  w = v
              OBVIOUS
        <2>1. a + 0 = a
              OBVIOUS
        <2> QED BY <2>1, QuorumUnique
  <1>step. \A k \in Nat : P(k) => P(k + 1)
        \* This is the mathematical core of Ben-Or safety, and the LAST open obligation in
        \* the IndInv => AgreementInv direction. The forward chain is:
        \*   ExistsQuorum2LessRam(a+k+1, w)  -- a D2(w) quorum at round a+k+1
        \*     => CorrectD2Exists: a CORRECT D2(w) sender at a+k+1
        \*     => Lemma7: a type-1 majority for w at a+k+1
        \*     => MajorityIntersect/Lemma9: a correct msgs1[a+k+1] message has value w,
        \*        and (Lemma9 at a+k) that value lies in SupportedValues(a+k); so
        \*        w \in SupportedValues(a+k).
        \* The GAP: closing this needs `w \in SupportedValues(a+k) => w = v`, but the
        \* induction hypothesis P(k) only says "a D2-QUORUM at a+k is v" -- which is too
        \* weak (it is vacuously true when no quorum exists at a+k, and a quorum does not
        \* persist across rounds since each round has its own msgs2). ExistsQuorum2LessRam
        \* and SupportedValues are also not interchangeable (one counts messages with
        \* 2*nv>N+T, the other counts senders with |Others|<N-2T). To close it, STRENGTHEN
        \* the induction predicate to track the value lock directly, e.g.
        \*   P'(k) == v \in SupportedValues(a+k) /\ SupportedValues(a+k) \subseteq {v}
        \* and prove SupportedValues(a+k) \subseteq {v} => SupportedValues(a+k+1) \subseteq {v}
        \* (correct values stay v, via Lemma9 + Lemma13 + Step2 reasoning), with base case
        \* ExistsQuorum2LessRam(a,v) => SupportedValues(a) = {v}. That is a multi-lemma
        \* redesign -- genuine research-level work, not a mechanical gap.
        OMITTED \* TODO: strengthen induction predicate to SupportedValues lock (see above)
  <1>all. \A k \in Nat : P(k)
        OMITTED \* TODO: NatInduction wiring depends on the strengthened lock induction step above.
  <1> QED
        \* map every r \in ROUNDS with r >= a to k = r - a \in Nat
        <2> SUFFICES ASSUME NEW r \in ROUNDS, r >= a, NEW w \in VALUES,
                            ExistsQuorum2LessRam(r, w)
                     PROVE  w = v
              OBVIOUS
        <2>1. (r - a) \in Nat /\ a + (r - a) = r
              BY RoundsNat
        <2>2. P(r - a)
              BY <1>all, <2>1
        <2> QED BY <2>1, <2>2

\* MAIN AGREEMENT THEOREM.
\* We assume TypeOK alongside IndInv (i.e. the full inductive invariant IndInit), since
\* AgreementInv needs the variable types (e.g. decision[id] \in VALUES).
THEOREM Agreement == TypeOK /\ IndInv => AgreementInv
  <1> SUFFICES ASSUME TypeOK, IndInv,
                      NEW id1 \in CORRECT, NEW id2 \in CORRECT,
                      decision[id1] /= NO_DECISION,
                      decision[id2] /= NO_DECISION
               PROVE  decision[id1] = decision[id2]
        BY DEF AgreementInv
  <1> USE DEF IndInv
  <1>1. round[id1] > 1 /\ ExistsQuorum2LessRam(round[id1] - 1, decision[id1])
        BY DEF Lemma1_DecisionRequiresLastQuorumLessRam
  <1>2. round[id2] > 1 /\ ExistsQuorum2LessRam(round[id2] - 1, decision[id2])
        BY DEF Lemma1_DecisionRequiresLastQuorumLessRam
  <1> DEFINE a1 == round[id1] - 1
  <1> DEFINE a2 == round[id2] - 1
  <1>3. /\ a1 \in ROUNDS /\ a2 \in ROUNDS
        /\ decision[id1] \in VALUES /\ decision[id2] \in VALUES
        \* round[id] \in ROUNDS = Nat (TypeOK) and round[id] > 1 => round[id]-1 \in Nat;
        \* decision[id] \in VALUES \cup {NO_DECISION} minus NO_DECISION.
        BY <1>1, <1>2, RoundsNat DEF TypeOK
  <1>4. CASE a1 <= a2
        \* v1's quorum at a1 locks round a2, where v2 also has a quorum => v2 = v1
        <2>1. \A r \in ROUNDS : r >= a1 =>
                (\A w \in VALUES : ExistsQuorum2LessRam(r, w) => w = decision[id1])
              BY <1>1, <1>3, LockLemma
        <2> QED BY <1>2, <1>3, <1>4, <2>1
  <1>5. CASE a2 <= a1
        <2>1. \A r \in ROUNDS : r >= a2 =>
                (\A w \in VALUES : ExistsQuorum2LessRam(r, w) => w = decision[id2])
              BY <1>2, <1>3, LockLemma
        <2> QED BY <1>1, <1>3, <1>5, <2>1
  <1> QED
        BY <1>3, <1>4, <1>5, RoundsNat

=============================================================================
