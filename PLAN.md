# DPlean4: Differential Privacy with Continuous Distributions in Lean 4

## Context

Build a noncomputable, measure-theoretic Lean 4 library for proving differential privacy (DP) of algorithms whose outputs may be continuous. The library is a specification and proof library: it will not implement real random sampling, extraction, floating-point arithmetic, or a probabilistic programming language such as SampCert's `SLang`.

The first convincing endpoint: a proof of the continuous Laplace mechanism, plus reusable postprocessing and sequential composition theorems. Approximate DP and the Gaussian mechanism follow after the pure-DP foundation is stable.

The library should support discrete, continuous, and mixed output measures through one API. Every privacy statement quantifies over measurable events — no point-probability functions.

**Note on milestone ordering**: Although both Laplace/pure-DP and Gaussian/zCDP are goals, this plan sequences them (Laplace first, Gaussian after) rather than running them in parallel. Reason: the Laplace vertical slice tests nearly every design choice — continuous events, ENNReal, measurability, density integration, parameter boundaries, adjacency, ergonomics — without the additional Rényi divergence burden. For a developer new to Lean 4, settling the core API through one complete example before starting the harder Gaussian/Rényi track avoids costly rework. The Gaussian track begins in Milestone 4 once the foundation is stable.

This plan incorporates a critical review from a separate analysis (CODEX_CONTINUOUS_DP_PLAN.md), which caught several issues in an earlier draft: defining DP via divergences instead of events, claiming kernels give composition "for free," uncritically adopting real-valued RN derivatives, proposing a premature abstract typeclass, and understating the Isabelle/HOL formalization's scope.

---

## Landscape

| System | Proof Assistant | Continuous? | Scope |
|--------|----------------|-------------|-------|
| **SampCert** (PLDI 2025) | Lean 4 | No — discrete `SLang` monad | Pure DP, zCDP, discrete Laplace/Gaussian, basic additive composition, postprocessing, parallel composition. ~12,000 lines. Deployed at AWS Clean Rooms |
| **CertiPriv** (POPL 2012) | Coq | No — discrete internally | Laplace, Gaussian, Exponential mechanisms via apRHL |
| **Sato & Minamide** (CPP 2025) | Isabelle/HOL | **Yes** | General DP statistical divergence, continuous Laplace (scalar + multidimensional), report noisy max, randomized response, postprocessing, group privacy, composition. Strongest existing continuous formalization, but does not cover zCDP, RDP, Gaussian mechanism, advanced composition, or subsampling |

### SampCert: what to reuse, what to avoid

**Reusable ideas** (proof strategies, not code):
- Adjacency relation separated from mechanism
- Generic privacy-system interfaces with monotonicity, composition, postprocessing
- Sensitivity predicates separate from mechanism definitions
- Proving distribution correctness separately from privacy
- zCDP → approximate DP conversion strategy (Markov inequality on MGF)
- Pure DP → zCDP conversion (ε²/2)

**Should not import as a dependency**: Its DP modules import `SLang`, its abstract class has discrete constraints (`Countable`, `DiscreteMeasurableSpace`), its noise interface requires integer-valued queries and rational parameters. There is also a suspicious version inconsistency: `lakefile.lean` requests Mathlib `v4.29.0` while `lean-toolchain` says Lean `v4.10.0` — this may be a transient branch error but requires a clean-room build audit before any reuse. Apache-2.0 license permits reuse with attribution, but every copied proof must be reviewed against continuous definitions and current Mathlib APIs.

### What no prover has formalized (as of Aug 2026)

This should be treated as a literature-search question to revisit, not a settled novelty claim:
- Continuous zCDP or RDP (SampCert has discrete zCDP; no continuous version found)
- Advanced composition theorem
- Privacy amplification by subsampling
- f-DP / Gaussian DP
- Exponential mechanism in Lean 4

---

## Mathlib Foundations

### Ready to use directly
- **Measures**: `MeasureTheory.Measure`, `IsProbabilityMeasure`, `SigmaFinite`, `AbsolutelyContinuous`
- **Probability measures**: `MeasureTheory.ProbabilityMeasure` — packages total mass 1 with measurable structure on the space of probability measures
- **Radon-Nikodym**: `rnDeriv`, `withDensity`, Lebesgue decomposition, chain rules
- **Integration**: Bochner + Lebesgue integrals, dominated/monotone convergence, Fubini
- **Markov kernels**: Full hierarchy (`IsMarkovKernel` → `IsSFiniteKernel`), `compProd` for adaptive joint experiments with Markov/s-finite closure and iterated-integral lemmas, `map`, `comap`, `withDensity`, disintegration
- **PDFs**: `HasPDF` typeclass, `pdf` as RN derivative of pushforward measure
- **Distributions**: Gaussian (on ℝ and Banach spaces — density, translation, scaling, convolution, moments, probability-measure instance), Exponential, Gamma, Uniform — **but NO Laplace**
- **KL divergence**: Defined for general σ-finite measures with Gibbs' inequality and converse. Chain rule already phrased using measures and Markov kernels
- **Log-likelihood ratio**: `llr μ ν x = log (μ.rnDeriv ν x).toReal` — exactly the privacy loss function. Measurability and scaling facts proved
- **Moments**: Variance, MGF (including complex), sub-Gaussian MGFs, Hoeffding's inequality, Azuma-Hoeffding
- **Independence & conditioning**: Full conditional expectation with tower property, Jensen's inequality
- **`measure.real`**: Exists but documentation warns the real-valued API is incomplete

### Must build ourselves
| Component | Why | Difficulty |
|-----------|-----|------------|
| **Laplace distribution** | Not in Mathlib; foundation of the Laplace mechanism | Medium |
| **Rényi divergence (continuous)** | Core of zCDP/RDP; SampCert only has discrete version | Hard |
| **Hockey-stick divergence** | Equivalent characterization of (ε,δ)-DP; useful for conversion theorems | Medium-Hard |

---

## Architecture

### Mechanism representation

Use probability measures for standalone mechanisms, with kernel bridges for composition:

```lean
-- Primary: mechanism as a function from databases to probability measures
-- The database type D need NOT be measurable
abbrev Mechanism (D O : Type*) [MeasurableSpace O] :=
  D → ProbabilityMeasure O
```

**Why not kernel-first?** A `Kernel` requires both input and output to be measurable spaces, but databases (e.g., `List T`) do not need a measurable structure for the elementary DP definition `∀ x x', Adjacent x x' → ...`. Using `D → ProbabilityMeasure O` avoids forcing databases into an artificial measurable space.

For adaptive composition (where the second mechanism depends measurably on the first's output), provide a kernel-facing layer using Mathlib's `Kernel.compProd`. This layer requires measurability of the continuation — do not hide that obligation behind an unrestricted monadic `bind`.

During Milestone 1, prototype both representations and select the public API after proving postprocessing and adaptive-composition examples in both. Expected outcome: function representation for user-facing mechanisms, with kernel bridges for composition.

### Privacy definition: events first, divergences second

Define DP directly via the standard measurable-event inequality. Do **not** define it as "bounding a divergence" — that reverses the logical dependency and forces premature divergence API choices.

For `μ ν : ProbabilityMeasure O`, the one-way approximate-DP relation:

```
∀ s, MeasurableSet s → μ(s) ≤ exp(ε) * ν(s) + δ
```

Use `ε δ : NNReal` coerced to `ENNReal`. Use the **multiplicative** form (not SampCert's division form — division over `ENNReal` introduces zero/∞ side conditions). Do not build `δ ≤ 1` into the core relation: it remains algebraically meaningful for any nonneg `δ`; add `ValidParams` as a separate predicate.

Keep the one-way measure comparison separate from adjacency symmetry. Define a mechanism as DP by applying the comparison to every directed adjacent pair. This permits directed adjacency but recovers the usual two directions when adjacency is symmetric.

For pure DP, prove equivalences among:
1. Event domination `μ ≤ exp(ε) • ν` as measures
2. The pointwise inequality on all measurable events
3. A density/Radon-Nikodym bound (under absolute continuity)

Divergences (hockey-stick, max, Rényi) are built as equivalent proof interfaces **after** the event-based definition works, not as the primary definition.

### ENNReal strategy

The primary event inequality uses `ENNReal`. Do not blanket-switch to real-valued RN derivatives — converting `rnDeriv` to real can silently lose `∞`. Follow Mathlib's own `llr`/KL pattern: use `ENNReal` for nonneg densities and event bounds; cross to `ℝ` locally under explicit finite-measure and absolute-continuity hypotheses.

### Adjacency

Adjacency is a **parameter** (a relation), not a typeclass with one canonical instance per type. A single database type can have multiple meaningful adjacency relations (add/remove, replace-one, bounded vs unbounded), so baking one choice into a typeclass would be wrong.

```lean
-- Adjacency is a relation parameter, not a typeclass
-- DP definitions and theorems are parameterized over it:
--   variable (adj : D → D → Prop)

-- Supply standard adjacency definitions:
def ListAddRemove (l₁ l₂ : List T) : Prop := ...  -- unbounded DP
def ListReplace   (l₁ l₂ : List T) : Prop := ...  -- bounded DP
-- With symmetry proofs where appropriate
```

Do not hard-wire adjacency to `List T` with add/delete. Supply standard relations as definitions. Theorem statements must always show which adjacency relation is in scope.

### No premature abstract typeclass

Do **not** create an abstract `DPSystem` typeclass with composition/postprocessing as fields before the concrete theorems exist. That would assume the foundational results this project aims to verify. Extract such an interface only after the concrete theorems for pure DP, approximate DP, and zCDP are all proved, and keep the proved theorems available independently of any typeclass.

### Module layout

```
DPlean4/
  Basic/
    Adjacency.lean            -- Generic adjacency, list instances
    Sensitivity.lean          -- L1, L2 sensitivity for generic adjacency
  Probability/
    Mechanism.lean            -- D → ProbabilityMeasure O
    KernelBridge.lean         -- Kernel-based adaptive composition layer
  Privacy/
    MeasureClose.lean         -- One-way ε,δ event inequality
    Pure.lean                 -- Pure ε-DP (δ=0 specialization + equivalences)
    Approximate.lean          -- (ε,δ)-DP definition and properties
    Postprocessing.lean       -- Deterministic measurable postprocessing
    Composition.lean          -- Independent + adaptive sequential composition
    RenyiDP.lean              -- Rényi DP definition (built after Divergence/Renyi)
    ZeroCDP.lean              -- zCDP definition and conversions
  Divergence/                 -- Built AFTER event-based API works
    HockeyStick.lean          -- Supremum formulation, equivalence with MeasureClose
    Renyi.lean                -- Rényi divergence for measures (α > 1)
  Distribution/
    Laplace.lean              -- Density, normalization, translation, moments
  Mechanism/
    Laplace.lean              -- Continuous Laplace mechanism, ε-DP proof
    Gaussian.lean             -- Continuous Gaussian mechanism, (ε,δ)-DP and zCDP
    Exponential.lean          -- Exponential mechanism
  Examples/
    RandomizedResponse.lean   -- Discrete regression test
    ReportNoisyMax.lean       -- Continuous Laplace noise
```

Keep distributions independent of DP. Keep adjacency generic.

---

## Milestones

### Milestone 0: Project skeleton + Lean 4 ramp-up (Weeks 1-2)
**Goal**: Reproducible build, CI, familiarity with key Mathlib APIs.

| Task | Difficulty | Notes |
|------|-----------|-------|
| Install Lean 4 + elan + lake | Easy | https://leanprover-community.github.io/install/linux.html |
| Create `lakefile.lean` with Mathlib dep, pin compatible Lean + Mathlib versions | Easy | Use `lean-toolchain` to pin. First build fetches ~2GB oleans |
| Set up CI with `lake build`, `#print axioms` checks, forbid `sorry` in release modules | Easy-Medium | Record licenses for any reused code |
| Read/experiment with Mathlib APIs in scratch files | Learning | `Measure`, `ProbabilityMeasure`, `AbsolutelyContinuous`, `rnDeriv`, `withDensity`, `Kernel`, `gaussianReal` |
| Study SampCert's proof structure (read-only) | Learning | Build SampCert at a known-good commit separately; map reusable proof ideas. Focus on `Pure/DP.lean`, `ZeroConcentrated/DP.lean`, `Abstract.lean` |

**Lean 4 resources**: Mathematics in Lean, Mathlib docs, Lean Zulip.

**Acceptance**: clean checkout builds in CI; deliberate failing examples verify that `sorry`-checks run.

### Milestone 1: Measure-level DP foundation (Weeks 3-5)
**Goal**: Core DP definitions + basic properties, working for both discrete and continuous outputs.

| Task | Difficulty | Notes |
|------|-----------|-------|
| Define adjacency as a relation parameter + standard definitions (list add/remove, replace-one) | Easy | With symmetry proofs. Adjacency is a parameter, not a typeclass — see Architecture |
| Define `Sensitivity` (L1, L2) for real-valued queries over generic adjacency | Easy | |
| Define `MeasureClose ε δ μ ν` — the one-way event inequality | Medium | `∀ s, MeasurableSet s → μ(s) ≤ exp(ε) * ν(s) + δ` with `ε δ : NNReal` |
| Define `PureDP` and `ApproxDP` for mechanisms | Medium | Via `MeasureClose` applied to all adjacent pairs |
| Prove reflexivity at (0,0), parameter monotonicity, symmetry via adjacency symmetry | Easy-Medium | |
| Prove deterministic constant mechanism is (0,0)-DP | Easy | |
| Prove pure-DP → approximate-DP conversion | Easy | Set δ=0 |
| Prove event formulation / measure-order equivalence for pure DP | Medium | `μ ≤ exp(ε) • ν` as measures ↔ pointwise event inequality |
| Prototype kernel-based representation alongside function-based | Medium | Resolve public API choice by proving same examples in both |

**Acceptance**: definitions instantiate both a finite randomized-response mechanism and a continuous measure without any countability assumption on outputs.

### Milestone 2: Postprocessing, composition, and Laplace distribution (Weeks 6-9)
**Goal**: Basic proof rules + Laplace distribution ready for the mechanism proof.

| Task | Difficulty | Notes |
|------|-----------|-------|
| Prove deterministic measurable postprocessing | Medium | If M is (ε,δ)-DP and f is measurable, f∘M is (ε,δ)-DP |
| Prove independent product composition | Medium | (ε₁,δ₁) ⊗ (ε₂,δ₂) → (ε₁+ε₂, δ₁+δ₂) |
| Prove basic group privacy (chaining along a finite adjacency path) | Medium | |
| Prototype adaptive composition via `Kernel.compProd` | Hard | Identify exact measurability/integration lemmas needed. If blocked, produce a written list of missing lemmas rather than installing axioms |
| Define Laplace density on ℝ with strictly positive scale | Medium | `(2b)⁻¹ exp(-|x-μ|/b)`, b > 0 in primary constructor. Handle nonpositive scale separately; never use that branch implicitly in a privacy theorem |
| Prove Laplace density: nonnegativity, measurability, integral normalization | Medium | Follow `GaussianPDFReal` pattern from Mathlib |
| Prove Laplace probability-measure instance, `HasPDF`, translation law | Medium | |
| Prove pointwise density-ratio bound for shifted Laplace laws | Medium | `f(t;μ₁,b)/f(t;μ₂,b) ≤ exp(|μ₁-μ₂|/b)` via triangle inequality |

**Key risk**: Laplace distribution from scratch is the first real test of the infrastructure. The Isabelle formalization (Sato & Minamide) provides a theorem checklist but cannot be mechanically transliterated — Isabelle and Lean expose different measurability, integration, and probability APIs.

### Milestone 3: Continuous Laplace mechanism — first flagship (Weeks 10-13)
**Goal**: No-`sorry` privacy proof of the scalar Laplace mechanism. This is the project's first convincing result.

| Task | Difficulty | Notes |
|------|-----------|-------|
| Define real-valued query sensitivity for generic adjacency | Easy | |
| Define Laplace mechanism: add Lap(0, Δ/ε) noise to query output | Medium | As `Mechanism (List T) ℝ` (i.e., `List T → ProbabilityMeasure ℝ`) |
| Prove Laplace mechanism satisfies pure ε-DP | Medium-Hard | Combine density-ratio bound with sensitivity. Core calculation is clean; measure-theoretic bookkeeping (absolute continuity, integrating the density ratio over measurable sets) is where the work is |
| Handle boundary cases explicitly | Medium | ε=0 with zero sensitivity → adjacency-invariant query → 0-DP. Positive sensitivity with ε=0 → no finite calibration exists. Do not manufacture a theorem via Lean's division-by-zero |
| Prove a vector/product extension or clear L1 composition path | Medium-Hard | Show how the scalar result composes for multidimensional queries |
| Regression examples at boundary parameters | Easy | |
| `#print axioms` audit of the flagship theorem | Easy | Must show only expected classical/choice/quotient axioms |
| End-to-end composition round-trip | Medium | Define a concrete query, prove sensitivity, add noise, compose two mechanisms, verify final bound matches hand calculation |

**Acceptance**: a no-`sorry`, axiom-audited theorem for the scalar Laplace mechanism over Borel ℝ, with literature citation and plain-language restatement.

### Milestone 4: Approximate DP toolkit + Gaussian mechanism (Weeks 14-20)
**Goal**: (ε,δ)-DP infrastructure, Gaussian mechanism, and Rényi divergence research spike.

| Task | Difficulty | Notes |
|------|-----------|-------|
| Define hockey-stick divergence: `HS(γ, μ, ν) = sup { μ.real(s) - γ * ν.real(s) }` | Medium-Hard | Use `γ = exp ε`. Probability finiteness makes the set bounded. Compare real-valued vs EReal formulation before freezing API. **Do not use ENNReal truncated subtraction (`tsub`)** without proving it equals the intended signed difference — `tsub` silently floors at 0, which could mask bugs in the divergence definition |
| Prove `MeasureClose ε δ μ ν ↔ HS(exp ε, μ, ν) ≤ δ` | Medium | |
| Complete adaptive sequential composition with explicit measurable continuations | Hard | Prove (ε₁+ε₂, δ₁+δ₂) bound from first principles using kernels/iterated integrals |
| Prove parallel composition | Hard | Needs database decomposition / disjoint-access hypothesis, not just probabilistic independence |
| Develop Gaussian tail inequalities needed for calibration | Medium-Hard | May expose Mathlib gaps |
| Prove shifted-Gaussian density/privacy-loss lemmas | Medium | Reuse Mathlib's `gaussianReal` |
| Prove Gaussian mechanism satisfies (ε,δ)-DP with exact calibration | Hard | σ ≥ Δ₂ √(2 ln(1.25/δ)) / ε. State parameter side conditions explicitly; cite exact paper reference |
| **Research spike**: Define Rényi divergence for α > 1 | Hard | Design note first: codomain, behavior when μ ⊀ ν, zero/∞ conventions. Prefer total extended-valued definition with specialized finite lemmas |
| Prove Rényi self-equality, shifted-Gaussian formula | Hard | D_α(N(μ₁,σ²) ∥ N(μ₂,σ²)) = α(μ₁-μ₂)²/(2σ²) |
| Inventory general lemmas needed (data processing, products) | Research | |
| Only after spike succeeds: add zCDP/RDP definitions and conversions | Hard | Borrow SampCert proof ideas only after generalizing discrete sums to measures |

**Acceptance**: a theorem for a named, literature-cited Gaussian calibration whose Lean statement has been independently checked against the paper, plus numerical sanity checks.

### Milestone 5: Algorithm library + ergonomics (Weeks 21+)
**Goal**: Nontrivial end-to-end algorithms, proof combinators, extensibility decisions.

| Task | Difficulty | Notes |
|------|-----------|-------|
| Randomized response (discrete regression test) | Medium | Tests generic API works for discrete outputs |
| Report noisy max with continuous Laplace noise | Hard | Reference: Sato & Minamide's ~1000-line Isabelle proof |
| Exponential mechanism over a base measure | Hard | Require measurability of utility and finite nonzero normalizer as explicit hypotheses |
| Proof combinators, simp lemmas, namespace discipline | Medium | |
| Decide next extension based on experience | — | Advanced composition, subsampling amplification, Rényi DP, zCDP, or coupling rules |

**Acceptance**: two nontrivial end-to-end algorithms (one continuous + compositional) proved without unfolding measure construction internals in user code.

---

## Difficulties and Risks

### Fundamental mathematical/formalization difficulties

| # | Risk | Impact | Notes |
|---|------|--------|-------|
| D1 | **Measurability is pervasive** | High | `map`, `bind`, parameterized measures, densities, adaptive continuations all need measurable hypotheses. Hiding them makes definitions false; exposing all makes the API unusable |
| D2 | **`ENNReal` arithmetic is subtle** | High | Coercions from `NNReal`/`ℝ`, `∞`, division by zero, distributivity side conditions dominate proofs. Prefer multiplication and finite probability bounds over division |
| D3 | **Parameterized-law measurability** | High | Not enough that every fixed Laplace law is a probability measure. Adaptive composition may need the map from location/scale parameters to probability measures to be measurable |
| D4 | **Density bounds → event bounds** | Medium | "Integrate both sides" requires measurable nonneg densities, restricted integrals, careful `ae` reasoning |
| D5 | **Radon-Nikodym side conditions** | Medium | Absolute continuity and Lebesgue decomposition must be explicit. Degenerate Gaussians/Dirac measures break naive density formulas |
| D6 | **Approximate composition** | High | Direct event manipulations for bind require Tonelli-style arguments and measurable kernels. Divergence formulation may simplify, but equivalence itself is substantial |
| D7 | **Gaussian calibration constants** | Medium | Exact constants, parameter regimes, log/sqrt domains, tail theorems are error-prone and may expose Mathlib gaps |
| D8 | **Higher-dimensional laws** | Medium | Mathlib's best Gaussian is on ℝ; multivariate mechanisms may need product constructions |
| D9 | **Boundary cases** | Medium | ε=0, δ=0/1, zero sensitivity, zero variance, nonpositive Laplace scale, empty datasets need intentional semantics and tests |
| D10 | **Rényi divergence integrability** | High | `∫ (dμ/dν)^α dν` requires integrability for fractional α > 1. Tractable for specific distributions; general theory requires conditions on the density ratio |
| D11 | **Adjacency conventions** | Low | Add/remove vs replace-one change sensitivities and constants. Theorem statements must be explicit |
| D12 | **Divergence conventions** | Medium | Rényi orders, log bases, hockey-stick parameterization, max-divergence codomains, behavior without absolute continuity vary across sources. Need reference citations and boundary tests |

### Engineering and ecosystem risks

| # | Risk | Impact | Notes |
|---|------|--------|-------|
| D13 | **Fast-moving Mathlib** | Medium | API renames/generalizations happen. Pin exact versions; controlled upgrade PRs |
| D14 | **Compile time** | Medium | Importing all measure theory into every file slows iteration. Profile module boundaries |
| D15 | **Upstream API gaps** | Medium | Laplace distribution and some kernel lemmas are missing. Isolate project-local lemmas for eventual upstream |
| D16 | **Premature abstraction** | Medium | SampCert's `DPSystem` assumes one additive parameter and approximate-DP conversion. A premature typeclass could make (ε,δ), RDP, zCDP awkward |
| D17 | **No executable semantics** | Low | This scope proves ideal mathematical mechanisms, not correctness of floating-point samplers. Documentation must state this boundary |

### Soundness and code-reuse risks

| # | Risk | Notes |
|---|------|-------|
| D18 | **A compiling proof can formalize the wrong theorem** | Every flagship statement needs plain-language restatement, literature citation, and review of adjacency + parameter conventions |
| D19 | **Imported code may hide assumptions** | Inspect imports, typeclass assumptions, axioms, `noncomputable`, degenerate branches before reuse |
| D20 | **Version drift invalidates audits** | Record source commits, not links to moving `main` branches |
| D21 | **Broad `aesop`/`simp` can hide brittle steps** | Retain intermediate lemmas in foundational inequalities |

---

## Validation Policy

For every imported or adapted result:
1. Record origin, commit/tag, license, and corresponding mathematical source
2. Restate the claim independently; check adjacency, parameter domains, event measurability, symmetry
3. Read the full dependency chain; search for `axiom`, `sorry`, unusual local instances
4. Reprove small foundational claims directly when cheaper than trusting a complicated port
5. Add adversarial boundary tests and at least one finite-model sanity check
6. Run `#print axioms` on public headline theorems — results must be limited to expected classical/choice/quotient axioms
7. For each mechanism milestone: composition round-trip example (concrete query → sensitivity → noise → compose → convert → check bound matches hand calculation)

Numerical scripts may test constants and catch reversed inequalities, but they are not proof dependencies. Continuous mathematical privacy must not be advertised as an implementation guarantee for finite-precision sampling.

---

## Decisions to Revisit After the Laplace Milestone

These are deliberately deferred until concrete experience informs them:
- Whether mechanisms should publicly be functions into `ProbabilityMeasure`, probability kernels, or a wrapper supporting both
- Whether approximate DP should use `(ε, δ)` as two arguments or a validated parameter structure
- Whether hockey-stick divergence becomes the core definition or remains an equivalent proof interface
- Whether generalized privacy notions deserve a SampCert-like typeclass, a graded relational structure, or ordinary theorem families
- Which general results belong upstream in Mathlib (most likely the Laplace distribution) vs. in this package

The conservative recommendation is to optimize first for transparent mathematical statements and dependable composition proofs, not executable notation or maximal abstraction.

---

## What We Do NOT Build

- **SLang or any discrete sampling monad** — out of scope
- **Code extraction / runtime sampling** — we prove privacy, not implement samplers
- **Floating-point analysis** — we work in exact real arithmetic
- **Computational DP** — information-theoretic DP only
- **Abstract DP typeclass prematurely** — concrete theorems first, abstraction after
