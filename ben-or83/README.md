# Ben-Or (1983) — TLAPS safety proof

A machine-checked [TLAPS](https://proofs.tlapl.us/) proof that the randomized
consensus protocol of Ben-Or '83 satisfies **Agreement**, by way of an inductive
invariant.

The proof establishes two facts:

1. **`IndInv` is inductive** — `Init => IndInv` (base case) and
   `IndInv /\ [Next]_vars => IndInv'` (inductive step).
2. **`IndInv => AgreementInv`** — the inductive invariant implies agreement
   (no two correct replicas decide different values).

Together with type preservation (`TypeOK`) these give safety of the protocol.

## Files

| File | Contents |
|------|----------|
| `Ben_or83.tla` | The protocol specification (`Init`, `Next`, `AgreementInv`, message constructors `D2`/`Q2`). |
| `Ben_or83_inductive.tla` | `TypeOK`, the inductive invariant `IndInv` (Lemmas 1–13) and `IndInit`. |
| `Ben_or83_proofs.tla` | The TLAPS proof (the file you verify). ~6250 lines, ~6147 obligations. |
| `typedefs.tla`, `Variants.tla` | Supporting modules required on the search path. |
| `MC_*.tla` | Apalache model-checking configurations used to *discover* / cross-check the invariant. |

The proof is organized into sections:

- **A** — foundational cardinality / quorum lemmas.
- **B** — type preservation + base case (`InitInd`).
- **C** — the `[Next]_vars` inductive step, one `Pres_Lemma<n>` per invariant
  conjunct (`Inductive` assembles them).
- **D** — `IndInv => AgreementInv` via the strict-quorum cross-round lock
  (`LockLemma`, `CrossRoundStrictQuorum`, `Agreement`).

## Prerequisites

- **TLAPS** (`tlapm`). This proof was checked with build `b064bce-dirty`
  installed via OPAM:

  ```sh
  export PATH="$HOME/.opam/<switch>/bin:$PATH"   # e.g. .opam/5.1.0/bin
  tlapm --version
  ```

- The standard TLAPS library (ships with `tlapm`, provides `TLAPS` and
  `FiniteSetTheorems`).
- `Variants.tla` must be on the search path. A copy lives in this directory; if
  you remove it, copy it back from your Apalache checkout
  (`src/tla/Variants.tla`).

> **Note.** This environment has **no Isabelle backend**. All obligations are
> discharged by Zenon and the SMT backend, which is sufficient for this proof.

## Verifying the proof

From this directory:

```sh
export PATH="$HOME/.opam/5.1.0/bin:$PATH"
tlapm --stretch 2 --threads 4 -I . Ben_or83_proofs.tla
```

Expected output:

```
[INFO]: All 6147 obligations proved.
```

and exit code `0`.

Flags:

- `-I .` adds the current directory to the module search path (for
  `Ben_or83_inductive`, `Ben_or83`, `typedefs`, `Variants`).
- `--stretch 2` doubles the per-obligation backend timeout (some quorum /
  cardinality obligations are slow).
- `--threads 4` runs backends in parallel.

### Timing and the fingerprint cache

`tlapm` caches discharged obligations in `.tlacache/`. A **cold** run (empty
cache) takes roughly **50 minutes**; a **warm** re-run after a small edit takes
a few minutes, since only changed obligations (and their dependents) are
re-checked. Delete `.tlacache/` to force a full re-verification from scratch.

### Verifying a single theorem

To re-check just part of the file (e.g. while editing), use the toolbox method
flag with a line range:

```sh
tlapm -I . --toolbox <startLine> <endLine> Ben_or83_proofs.tla
```

## Trusted base

The proof rests on a small set of explicitly stated assumptions at the top of
`Ben_or83_proofs.tla`:

- `NatInductionTrusted` — the natural-number induction principle (a TLAPS stdlib
  theorem; trusted here as an axiom to avoid the Isabelle-backed library proof).
- The protocol resilience bounds: `N > 5*T`, `0 <= F <= T`, `CORRECT`/`FAULTY`
  disjoint and finite with `|CORRECT| = N-F`, `|FAULTY| = F`, and
  `N, T, F \in Nat`.
- `RoundsNat` — `ROUNDS = Nat \ {0}` (rounds are numbered from 1).
- `NoDecisionNotValue` — `NO_DECISION \notin VALUES`.
- `VariantAx` — the round-trip facts for the `D2`/`Q2` message variants
  (provable from the community `Variants` module; stated as an axiom to keep the
  file self-contained).

There are **no `OMITTED` / admitted obligations** — every proof leaf is
discharged by a backend.
