# Second order term of Riesz energy on sphere

This repository contains a Lean 4 formalization of the main result of the paper
*Second order term of Riesz energy on sphere* by Damien Galant, Javier
Gómez-Serrano, Alexander Kaneko, Liudmyla Kryvonos, Lukas Liehr, and Mitchell A.
Taylor.

## Lean-verified main result

Let $d\geq 2$ and $-2<s<d$, with $s\neq 0$. For a configuration
$X=\{x_1,\ldots,x_N\}$ of $N$ distinct points on the unit sphere
$\mathbb{S}^d\subset\mathbb{R}^{d+1}$, define

$$
K_s(x,y)=\frac{1}{s}\lVert x-y\rVert^{-s},
\qquad
E_s(X)=\sum_{i\neq j}K_s(x_i,x_j),
\qquad
\mathcal{E}_s(\mathbb{S}^d;N)
=\inf_{\substack{X\subset\mathbb{S}^d\\ |X|=N}}E_s(X).
$$

The sum is over ordered pairs of distinct points, and the distance is chordal.
For $s>0$, this is the usual Riesz energy minimization problem; for $s<0$, it
is equivalent to maximizing the sum of the distance powers.
Let $\sigma_d$ be normalized surface measure, and write

$$
V_s(\mathbb{S}^d)
=\int_{\mathbb{S}^d}\int_{\mathbb{S}^d}
K_s(x,y)\,d\sigma_d(x)\,d\sigma_d(y),
\qquad
\omega_d=\mathcal{H}^d(\mathbb{S}^d).
$$

We provide a Lean verification of the following statement, which includes
Theorem 1.1 of the paper.

**Theorem.** For every integer $d\geq 2$ and every real $-2<s<d$, $s\neq 0$,
there is a finite constant $e_{s,d}$ such that

$$
\mathcal{E}_s(\mathbb{S}^d;N)
=V_s(\mathbb{S}^d)N^2
+\frac{e_{s,d}}{\omega_d^{s/d}}N^{1+s/d}
+o \left(N^{1+s/d}\right),
\qquad N\to\infty.
$$

Equivalently,

$$
\lim_{N\to\infty}
\omega_d^{s/d}
\frac{\mathcal{E}_s(\mathbb{S}^d;N)-V_s(\mathbb{S}^d)N^2}
     {N^{1+s/d}}
=e_{s,d}.
$$

Moreover,

$$
e_{s,d}=\inf_{P\in\mathcal{P}_d}W_{s,d}(P),
$$

where $\mathcal{P}_d$ is the class of stationary simple point processes in
$\mathbb{R}^d$ with intensity one and finite local second moments, and
$W_{s,d}$ is the Euclidean energy defined in Section 4 of the paper. This
infimum is attained by a process in $\mathcal{P}_d$, and

$$
e_{s,d}<0\quad\text{if }0<s<d,
\qquad
e_{s,d}>0\quad\text{if }-2<s<0.
$$


This establishes the existence of the second-order coefficient conjectured by
Brauchart, Hardin, and Saff. The conjectured formulas for that coefficient in
terms of particular lattices remain open.

The formal statement is
[`RieszShowcase.main_theorem`](Showcase_WithProofs.lean). In the Lean files,
the paper's $\mathcal{E}_s$ and $V_s$ are named `E_K` and `V_K`.
The names `E_s` and `V_s` refer to energies without the factor $1/s$;
the theorem also gives their asymptotic expansion with coefficient
$C_{s,d}=s\,e_{s,d}<0$.

**Dependencies:** The proved theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`, as checked by
[ProofAudit.lean](ProofAudit.lean).

## Build and verification

### Lean entry points

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

### Build

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

### Repository layout

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

### Reused source notices

The Bochner modules retain their existing copyright headers, upstream
[provenance](Riesz/Analysis/Bochner/provenance.json), and
[Apache-2.0 license](Riesz/Analysis/Bochner/LICENSE). That license accompanies
those reused modules; no repository-wide license is assigned here.
