# Build and verification

## Lean entry points

| File | Purpose |
| --- | --- |
| [Showcase.lean](Showcase.lean) | All 28 definitions and the statement of `RieszShowcase.main_theorem`, with one intentional `sorry` in place of the proof. Imports only Mathlib modules. |
| [Showcase_WithProofs.lean](Showcase_WithProofs.lean) | The identical theorem statement with its complete proof. Uses the definitions from `Riesz/Definitions.lean`. |
| [Riesz.lean](Riesz.lean) | Umbrella module for the proof library. |
| [Riesz/Asymptotics/VerifiedMain.lean](Riesz/Asymptotics/VerifiedMain.lean) | Assembly of the main theorem. |
| [ProofAudit.lean](ProofAudit.lean) | Checks that the proved public theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. |
| [comparator.json](comparator.json) | Comparator configuration pairing both showcases and all 28 definitions. |

The two showcase modules are alternative entry points and must be imported
separately: they deliberately use the same declaration names. To use the proved
public theorem in another Lean file, write `import Showcase_WithProofs`.
The proof library and axiom audit do not import the statement-only showcase.

## Build

Install [elan](https://github.com/leanprover/elan), the Lean toolchain manager,
and Git. In the repository root, run:

```sh
lake exe cache get
lake build
```

The toolchain is Lean `v4.32.2`. Mathlib is pinned to
`905b95818eb32af7874a58b427f50c1711a5e96c`; its transitive dependencies are
pinned in [lake-manifest.json](lake-manifest.json). Lake downloads dependencies
into `.lake/packages`. No existing local Mathlib checkout is required.

The default build checks the proof library, both showcases, and the axiom audit.
The single `sorry` warning from `Showcase.lean` is expected. The proved showcase
and its proof library contain no placeholders.

To build just the proved entry point and its axiom audit:

```sh
lake build Showcase_WithProofs ProofAudit
```

To rerun the axiom check directly:

```sh
lake env lean ProofAudit.lean
```

The `#guard_msgs` check makes a changed axiom report a build error.

## Repository layout

| Path | Contents |
| --- | --- |
| [Riesz/Definitions.lean](Riesz/Definitions.lean) | Shared definitions used by the proofs. |
| [Riesz/Energy.lean](Riesz/Energy.lean) | Conversion between energy normalizations. |
| [Riesz/Analysis/](Riesz/Analysis/) | Gaussian, Fourier, and integral estimates. |
| [Riesz/Asymptotics/](Riesz/Asymptotics/) | Spherical limits and final theorem assembly. |
| [Riesz/Configuration/](Riesz/Configuration/) | Counting measures, laws, compactness, and moments. |
| [Riesz/Geometry/](Riesz/Geometry/) | Spherical geometry, coordinates, and count repair. |
| [Riesz/Negative/](Riesz/Negative/) | Finite-volume constructions, rounding, and the negative-exponent branch. |
| [Riesz/Stationary/](Riesz/Stationary/) | Stationary laws, Gaussian energies, and localization. |
| [Riesz/PastProjects/Problem1/](Riesz/PastProjects/Problem1/) | Reused supporting lemmas and their provenance record. |

## Reused source notices

The Bochner modules retain their existing copyright headers, upstream
[provenance](Riesz/Analysis/Bochner/provenance.json), and
[Apache-2.0 license](Riesz/Analysis/Bochner/LICENSE). That license accompanies
those reused modules; no repository-wide license is assigned here.
