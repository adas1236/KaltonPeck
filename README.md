# KaltonPeck

## General overview

This project formalizes results about the real Kalton--Peck space `Z_2`.
It develops the functional-analytic and symplectic machinery needed to prove a
rank-parity theorem for finite-rank perturbations of operators on `Z_2`.  The
main result specializes this parity theorem to show that the rank of `T^2 + 1`
is even whenever it is finite.  As a consequence, a hyperplane of `Z_2` cannot
carry a complex structure.

The top-level theorem statements are in `KaltonPeck.lean`:

- `rankParityGeneral` proves the abstract symplectic Fredholm rank-parity result.
- `rankParityZ2` applies it to `Z_2`.
- `noHyperplaneComplexStructure` derives the hyperplane obstruction.

## Project setup

The project uses Lean `v4.31.0`, as pinned in `lean-toolchain`, together with
Mathlib and the dependencies recorded in `lake-manifest.json`.

1. Install [elan](https://github.com/leanprover/elan), Lean's version manager.
2. Clone this repository and enter its root directory.
3. Fetch dependencies (needed when `lake-manifest.json` is absent or has changed):

   ```sh
   lake update
   ```

4. On a fresh checkout, fetch Mathlib's compiled cache to avoid rebuilding
   dependencies from source:

   ```sh
   lake exe cache get
   ```

5. Compile the project:

   ```sh
   lake build
   ```

## File structure

Only the Lean formalization files are shown below.  `KaltonPeck.lean` is the
entry point; the files under `Support/` provide the results used by its three
top-level theorems.

```text
KaltonPeck.lean                         Main theorems: rank parity for Z_2 and the no-hyperplane-complex-structure result.
KaltonPeck/
├── Support/
│   ├── Definitions.lean                Core definitions for forms, Fredholm operators, ranks, and complex structures.
│   ├── Forms.lean                      Duality, annihilators, and symplectic-adjoint facts.
│   ├── Fredholm.lean                   Fredholm invariance, kernels, cokernels, and index calculations.
│   ├── FiniteParity.lean               Finite-dimensional parity results for alternating forms and complex structures.
│   ├── FiniteCodim.lean                Finite-codimension symplectic reduction and parity theorem.
│   ├── PathParity.lean                 Parity invariance along paths of Fredholm operators.
│   ├── GeneralRank.lean                Constructs the form used in the abstract rank-parity argument.
│   ├── Coordinates.lean                The sequence-coordinate model and centralizer defining Z_2.
│   ├── Symplectic.lean                 Canonical and transported symplectic forms on models of Z_2.
│   ├── CanonicalPairing.lean           Pairing identities for the canonical Z_2 coordinate model.
│   ├── StrictlySingular.lean           Definition and basic properties of strictly singular operators.
│   ├── StrictlySingularAdd.lean        Auxiliary strictly-singular and biorthogonal-sequence lemmas.
│   ├── StrictlySingularHilbert.lean    Hilbert-space adjoint results for strictly singular operators.
│   ├── StrictlySingularHilbertCompact.lean
│   │                                  Compactness consequences in the Hilbert-space setting.
│   ├── HilbertGlidingHump.lean         Gliding-hump and block-sequence constructions in canonical l2.
│   ├── CgpBlockExtraction.lean         Extracts compact blocks from a failed upper-semi-Fredholm condition.
│   ├── CgpCompactRestriction.lean      Compact-restriction and biorthogonal construction tools.
│   ├── CgpStrictlySingularLifting.lean Lifts strictly-singular information through the canonical quotient.
│   ├── KernelNuclearCorrection.lean    Builds compact/nuclear corrections to kernels.
│   ├── GraphFredholm.lean              Establishes the Fredholm graph result used for Z_2.
│   └── TargetSupport.lean              Converts a hyperplane complex structure into the rank-one obstruction.
│
└── Basic.lean                          Minimal starter example; not used by the main formalization.
```
