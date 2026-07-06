# Single-height Tendermint — machine-checked safety proof

A [TLAPS](https://proofs.tlapl.us/) proof that the single-height Tendermint
consensus algorithm satisfies **Agreement**: no two correct processes decide
different values.

The model is the safety fragment of Tendermint restricted to one height, with a
fixed set of correct processes (`Corr`) and Byzantine-faulty processes
(`Faulty`), `N = 3T + 1` replicas tolerating up to `T` faults, and a bounded
number of rounds (`MaxRound`). Faulty replicas may inject arbitrary messages.

## Files

| File | Contents |
|------|----------|
| `tendermint_single_indinv.tla` | The spec: state variables, the transition `Step` (10 correct actions + `FaultyStep`), the safety property `Agreement`, and the inductive invariant `TypedIndInv`. Machine-generated from a Wunderspec model — do not hand-edit. |
| `tendermint_single_indinv_proofs.tla` | The TLAPS proofs. |
| `README.md` | This file. |

## What is proved

Safety is established by the standard **inductive-invariant** argument, split
into three top-level theorems in `tendermint_single_indinv_proofs.tla`:

| Theorem | Statement | Meaning |
|---------|-----------|---------|
| `InitInd` | `Init => TypedIndInv` | the invariant holds in every initial state |
| `Inductive` | `TypedIndInv /\ Step => TypedIndInv'` | every transition preserves it |
| `AgreementThm` | `TypedIndInv => Agreement` | the invariant implies the safety property |

Together these give the usual conclusion: `TypedIndInv` holds in **every reachable
state** (by induction over runs, using `InitInd` for the base case and
`Inductive` for the step), and therefore `Agreement` holds in every reachable
state.

`Agreement` is
`\A p, q \in Corr : decision[p] = -1 \/ decision[q] = -1 \/ decision[p] = decision[q]`
(`-1` is the "undecided" marker), i.e. any two correct processes that have both
decided agree on the value.

### The invariant `TypedIndInv`

`TypedIndInv == IndTypeOk /\ IndInv`, where `IndTypeOk` is a typing invariant and
`IndInv` is a conjunction of **25** protocol invariants (in the spec). The
substantive ones are the cross-round *locking* invariants — e.g.
`PrecommitsLockValue` (a 2T+1 precommit quorum for a value at round `r0` blocks a
2T+1 prevote quorum for any other value in later rounds) and
`PrecommitLocksLaterPrevotes` — which are what ultimately force agreement across
rounds. `AgreementThm` closes the argument with quorum intersection (any two 2T+1
sets share a correct process, since `N = 3T + 1`).

> An earlier reduced invariant `TypedIndInvMin` (17 of the 25 conjuncts) was
> tried first; it is **not** inductive on its own (`PrecommitsLockValue` needs the
> extra 8 conjuncts), so the whole development now uses the full `TypedIndInv`.

### Assumptions

The proof is parametric in the constants and relies on these named `ASSUME`s /
`AXIOM` (near the top of the proofs module):

- `Neq3Tp1`: `N = 3*T + 1`, and `NgtT`: `N > 3*T` (the classic BFT threshold).
- `DisjointCF`: `Corr` and `Faulty` are disjoint; `NCard`: `N = |Corr| + |Faulty|`;
  `FiniteCF`: both are finite; `TgeF`: `T >= F` where `F == |Faulty|`.
- `ConstNat`: `N, T, MaxRound \in Nat`; `NilNotValid`: `-1 \notin ValidValues`;
  `ValidValuesNonEmpty`.
- `NatInductionTrusted`: ordinary induction over `Nat` (a trusted axiom, used for
  the round-descent arguments).

There are **no `OMITTED` proof steps** — every obligation is discharged.

## Checking the proofs with TLAPS

You need `tlapm` (the TLAPS proof manager) with its bundled backends
(**SMT / Zenon / Isabelle** — a handful of higher-order set-cardinality
obligations require the Isabelle backend). The standard TLAPS install provides
all three.

From this directory:

```sh
tlapm --stretch 2 --threads 3 -I . tendermint_single_indinv_proofs.tla
```

- `-I .` puts this directory on the module search path so the spec module is
  found (`FiniteSetTheorems` and `TLAPS` come from the TLAPS standard library).
- `--stretch 2` doubles the per-obligation prover timeouts (this is a large
  proof; several obligations are close to the default limit).
- `--threads 3` runs backends in parallel.

Expected result:

```
All 3769 obligations proved.
```

`tlapm` caches proved obligations in `.tlacache/`, so re-runs after an edit only
re-check what changed.

### A note on determinism

Some obligations are heavy (10–20 s of solver time, a few needing the Isabelle
fallback). On a **fully cold** run (`rm -rf .tlacache`) with `--threads 3`, a
small rotating handful can occasionally time out under CPU contention and be
reported as failed — a *warm* re-run (which re-attempts only those, with
everything else served from cache) clears them. For a deterministic single-pass
run from a cold cache, reduce contention or raise the margin:

```sh
tlapm --stretch 3 --threads 2 -I . tendermint_single_indinv_proofs.tla
```

The proofs themselves are complete and correct; the flakiness is purely
scheduling-related, and every obligation proves reliably in isolation.

### Checking a single theorem

To re-check just one theorem (e.g. while editing), use the Toolbox line-range
selector — pass the line span of the theorem:

```sh
tlapm --toolbox <startLine> <endLine> --stretch 2 -I . tendermint_single_indinv_proofs.tla
```
