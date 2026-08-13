# Plan for a Lean 4 Library for Continuous Differential Privacy

## 1. Goal and scope

Build a noncomputable, measure-theoretic Lean 4 library for proving differential privacy (DP) of algorithms whose outputs may be continuous. The initial library is a specification and proof library: it will not implement real random sampling, extraction, floating-point arithmetic, or a probabilistic programming language such as SampCert's `SLang`.

The first convincing endpoint should be a kernel-checked proof of the real-valued Laplace mechanism, plus reusable post-processing and sequential-composition theorems. Approximate DP and the Gaussian mechanism should follow after the pure-DP foundation is stable.

The project should support discrete, continuous, and mixed output measures through one API. It should not encode a continuous law as a point-probability function: every privacy statement must quantify over measurable events.

## 2. Landscape and findings

### SampCert

[SampCert](https://github.com/leanprover/SampCert) is the most substantial Lean 4 DP development found. Its PLDI 2025 paper reports more than 12,000 lines of proof, an abstract DP interface, composition and post-processing, pure DP and zero-concentrated DP (zCDP), and verified executable discrete Laplace and discrete Gaussian samplers ([paper](https://pages.cs.wisc.edu/~aws/papers/pldi25.pdf)). Its strongest reusable ideas are:

- an adjacency relation separated from the mechanism;
- generic privacy-system interfaces with monotonicity, composition, post-processing, and conversion to approximate DP;
- explicit sensitivity predicates;
- proving sampler/distribution correctness separately from privacy;
- proof engineering around difficult analytic results already available in mathlib.

Its probability representation is nevertheless deliberately discrete. `Mechanism T U` returns a `PMF U`; approximate and pure DP sum point masses over arbitrary sets; and `DiscProbSpace` requires `Countable` and `DiscreteMeasurableSpace` ([`Abstract.lean`](https://github.com/leanprover/SampCert/blob/main/SampCert/DifferentialPrivacy/Abstract.lean), [`Approximate/DP.lean`](https://github.com/leanprover/SampCert/blob/main/SampCert/DifferentialPrivacy/Approximate/DP.lean), [`Pure/DP.lean`](https://github.com/leanprover/SampCert/blob/main/SampCert/DifferentialPrivacy/Pure/DP.lean)). The paper explicitly defines mechanisms over countable ranges and describes the mass-function DSL as a choice made to support executable samplers. Thus the limitation is architectural, not just a missing real-valued instance.

SampCert should not be imported wholesale in the first release. Its DP modules import `SLang`, its abstract class has discrete constraints in composition/post-processing, and its noise interface is specialized to integer-valued queries and rational parameters. There is also currently a suspicious repository-version inconsistency: `lakefile.lean` requests mathlib `v4.29.0`, while `lean-toolchain` says Lean `v4.10.0`. This may be a transient branch error, but it is enough to require a clean-room build audit before reuse. The Apache-2.0 license permits reuse with attribution, but every copied proof should be reviewed against the continuous definitions and current mathlib APIs.

### Mathlib's probability and measure theory

Mathlib is the appropriate foundation, not a custom probability implementation.

- `MeasureTheory.Measure` supports arbitrary measurable spaces, `map`, restriction, products, integration, and a Giry-style `bind`; `bind` requires measurability of the measure-valued continuation ([Giry monad documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/GiryMonad.html)).
- `MeasureTheory.ProbabilityMeasure` packages a measure of total mass one and gives the space of probability measures a measurable structure ([documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.html)).
- Probability kernels have composition, deterministic kernels, integration, and Radon--Nikodym-related modules ([kernel sources](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Probability/Kernel)). Kernels are especially useful for adaptive composition because measurability is part of their interface.
- `withDensity`, absolute continuity, and `rnDeriv` provide the core tools for density ratios and privacy loss ([Radon--Nikodym documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.html)).
- Mathlib already defines the real-valued log-likelihood ratio `llr μ ν x = log (μ.rnDeriv ν x).toReal`, proves measurability and scaling facts, and develops KL divergence for general finite measures ([log-likelihood ratio](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.html), [KL divergence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/InformationTheory/KullbackLeibler/Basic.html)). Its KL chain rule is already phrased using measures and Markov kernels. This is highly relevant to later privacy-loss, Rényi, zCDP, and composition work, but KL itself does not define DP.
- Kernel `compProd` represents an adaptive joint experiment and comes with Markov/s-finite closure and iterated-integral lemmas ([documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/CompProd.html)). This is a likely foundation for adaptive composition rather than something the project should reimplement.
- Mathlib has kernel-aware sub-Gaussian MGFs and Hoeffding/Azuma--Hoeffding results ([documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/SubGaussian.html)). They may support advanced composition later, but substantial bridging work from privacy loss to those hypotheses remains.
- Mathlib already defines a real Gaussian measure and its density, translation/scaling laws, convolution, moments, and probability-measure instance ([Gaussian documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Real.html)).
- Mathlib also has an abstract `IsGaussian` predicate for measures on Banach spaces. It characterizes one-dimensional projections but does not by itself supply the concrete finite-dimensional density/Rényi formulas required for a multivariate Gaussian mechanism ([documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Basic.html)).
- Mathlib does not appear to provide a Laplace distribution as a standard named probability law. That distribution, its normalization, measurability, translation law, and density-ratio lemmas are therefore early project work.
- `measure.real` exists, but its own documentation warns that the real-valued API is incomplete. The primary event inequality should consequently use `ENNReal`; real-valued corollaries can be added only where finiteness conversions are well controlled ([documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Real.html)).

Mathlib is moving quickly. Pin one matching Lean/mathlib release, use only public APIs where possible, and run CI against the pin. Contributions that are general probability facts (for example a Laplace law) should eventually be proposed upstream, but the DP library must not wait on upstream acceptance.

### Other formalizations

The closest blueprint for continuous foundations is Sato and Minamide's Isabelle/HOL development, available in the [Archive of Formal Proofs](https://www.isa-afp.org/entries/Differential_Privacy.html) and described in their [CPP 2025 paper](https://arxiv.org/abs/2410.15386). It includes measurable list spaces, a Laplace distribution, a DP statistical divergence, basic DP properties, randomized response, one- and multidimensional Laplace mechanisms, and report noisy max. It is valuable as a theorem checklist and as an independent reference for edge conditions. Its proofs cannot be transliterated mechanically: Isabelle and Lean libraries expose different measurability, integration, and probability-monad interfaces.

Earlier systems such as CertiPriv/apRHL, Fuzz/Duet, and testing tools solve related but different problems. They motivate relational liftings, couplings, or automation, but are not Lean 4 continuous-measure libraries. Those features should not be prerequisites for the first usable release.

No other mature public Lean 4 package with foundational continuous DP proofs was found in this survey. This conclusion should be rechecked before major releases because the ecosystem is changing.

### Critical review of the companion `PLAN.md`

The companion plan contributes a useful inventory of `llr`, KL divergence, kernel composition-products, sub-Gaussian tools, Rényi/zCDP, the exponential mechanism, and end-to-end validation. Those items are incorporated here as later milestones and research spikes.

Several claims/designs should not be adopted without qualification:

- “No proof assistant handles continuous distributions beyond the basics” understates the Isabelle/HOL development, which includes a general DP divergence, multidimensional Laplace, and report noisy max. It is better described as the strongest existing continuous formalization but not a comprehensive modern DP library.
- “Continuous zCDP/RDP has never been done in any prover” was not established by the cited sources. Treat it as a literature-search question, not a novelty claim.
- Pure DP should not initially be *defined only* through a max-divergence supremum, nor approximate DP only through hockey-stick divergence. The direct measurable-event definition is standard, easy to audit, and avoids immediately choosing among `ENNReal`, `EReal`, and real subtraction. Divergences should be proved equivalent interfaces.
- The notation in the companion plan conflates the privacy parameter `δ` with the hockey-stick scale. A precise definition should use, for example, `HS γ(μ‖ν) = sup_s (μ(s) - γ ν(s))`, with `γ = exp ε`; then `(ε,δ)`-DP is `HS (exp ε)(μ‖ν) ≤ δ` (under a chosen real/extended-real encoding).
- Kernels do not make DP composition “free.” They provide the correct measurable construction; the privacy inequality through `comp`, `compProd`, or `map` still requires a nontrivial proof.
- Converting `rnDeriv` to real values is useful only after proving finiteness/non-infinity almost everywhere. A blanket “follow real-valued RN derivatives” rule can silently lose `∞`. The library should use `ENNReal` for nonnegative densities/event bounds and cross to `ℝ` locally under explicit finite-measure and absolute-continuity hypotheses, following mathlib's own `llr`/KL pattern.
- Laplace and Gaussian/Rényi work should not start in parallel in a small project. The Laplace vertical slice should settle the core API first; Rényi divergence is a separate high-risk milestone.
- An abstract DP typeclass with composition/post-processing as fields would assume the foundational results the project aims to verify. Extract such an interface only after the concrete theorems exist, and keep the proved theorems available independently of it.

## 3. Proposed architecture

### 3.1 Core representation

Use probability measures for standalone mechanisms and probability kernels for compositional structure.

Conceptually:

```lean
abbrev Mechanism (D O : Type*) [MeasurableSpace O] :=
  D → MeasureTheory.ProbabilityMeasure O
```

The database/input type `D` need not itself be measurable for the elementary DP definition. A separate kernel-facing layer should represent an adaptive continuation whose dependence on a prior output is measurable. Do not expose an unrestricted monadic `bind` that silently drops this obligation.

This hybrid avoids forcing all databases into an artificial countable space while using mathlib kernels where adaptive composition genuinely needs measurability. During Milestone 1, prototype two formulations:

1. `D → ProbabilityMeasure O` plus explicit measurable continuations;
2. a probability `Kernel` from a measurable input space.

Select the public API only after proving the same post-processing and adaptive-composition examples in both. Expected choice: the function representation for user-facing mechanisms, with kernel bridges for composition.

### 3.2 Privacy definition

For `μ ν : ProbabilityMeasure O`, define the one-way approximate-DP divergence/property by measurable events:

```text
∀ s, MeasurableSet s → μ(s) ≤ exp(ε) * ν(s) + δ.
```

Use `ε δ : NNReal` and coerce deliberately to `ENNReal`. Do **not** build `δ ≤ 1` into the core relation: the algebraic relation and its monotonicity/composition theorems remain meaningful for every nonnegative `δ`, while `δ ≤ 1` is a separate `ValidParams` predicate for user-facing guarantees. Keep the one-way measure comparison separate from adjacency symmetry; then define a mechanism to be DP by applying the comparison to every directed adjacent pair. This permits directed adjacency but recovers the usual two directions when adjacency is symmetric.

Prefer the multiplicative event inequality over SampCert's division form. Division over `ENNReal` introduces zero/`∞` side conditions and obscures the standard definition. For pure DP, prove equivalences among:

- event domination `μ ≤ exp ε • ν` as measures;
- inequalities on all measurable events;
- a density/Radon--Nikodym bound when absolute continuity hypotheses hold.

For approximate DP, introduce the hockey-stick/event divergence as a supremum only after the direct event API works. A good first candidate for probability measures is the real-valued bounded supremum

```text
HS γ μ ν = sup { μ.real(s) - γ * ν.real(s) | s is measurable },  γ ≥ 0,
```

because probability finiteness makes the set nonempty and bounded. Prove `MeasureClose ε δ μ ν ↔ HS (exp ε) μ ν ≤ δ`. Compare this candidate with an `EReal` formulation before freezing the public divergence API; do not use truncated `ENNReal` subtraction without proving it expresses the intended signed difference.

For later privacy-loss work, reuse mathlib's `llr` and KL APIs rather than creating incompatible duplicates. Before defining Rényi divergence, write a design note choosing its codomain and behavior when `μ ≪̸ ν`, the order regimes (`α > 1` first), and zero/`∞` conventions. Prefer a total extended-valued definition with specialized finite real-valued lemmas over a definition carrying integrability proofs as data.

### 3.3 Module layout

```text
DPlean4/
  Basic/Parameters.lean
  Basic/Adjacency.lean
  Probability/Mechanism.lean
  Probability/Kernel.lean
  Privacy/MeasureDomination.lean
  Privacy/Pure.lean
  Privacy/Approximate.lean
  Privacy/Composition.lean
  Privacy/Postprocessing.lean
  Sensitivity/Basic.lean
  Divergence/HockeyStick.lean
  Divergence/Renyi.lean
  Distributions/Laplace.lean
  Distributions/Gaussian.lean
  Mechanisms/Laplace.lean
  Mechanisms/Gaussian.lean
  Mechanisms/Exponential.lean
  Examples/RandomizedResponse.lean
  Examples/ReportNoisyMax.lean
```

Keep distributions independent of DP. Keep adjacency generic rather than hard-wiring lists. Supply standard list add/remove and replace-one adjacency as instances/definitions, with symmetry proofs where appropriate.

## 4. Milestones and acceptance criteria

### Milestone 0 -- Reproducible skeleton and audit harness

- Pin a mutually compatible stable Lean and mathlib release.
- Establish Lake package, formatting, docs, and CI using `lake build` and `lake test` (or compile-time example tests).
- Add `#print axioms` checks for headline results; forbid `sorry` in release modules.
- Record licenses and exact source/commit for any reused code.
- Build SampCert at a known-good tag/commit separately and map candidate reusable definitions and proof ideas; do not make it a dependency.

Acceptance: clean checkout builds in CI; deliberate failing examples demonstrate that the checks run; trust assumptions are documented.

### Milestone 1 -- Measure-level DP foundation

- Define parameters, adjacency, mechanisms, one-way measure closeness, pure DP, and approximate DP.
- Prove reflexivity at `(0,0)`, parameter monotonicity, symmetry handling through adjacency, deterministic constant privacy, and pure-to-approximate conversion.
- Prove event formulation/measure-order equivalence for pure DP.
- Resolve the public representation decision by completing function- and kernel-based prototypes.

Acceptance: the definitions instantiate both a finite randomized-response mechanism and a continuous measure without any countability assumption on outputs.

### Milestone 2 -- Basic proof rules and composition feasibility spike

- Deterministic measurable post-processing.
- Constant mechanisms and independent product composition.
- Basic group-privacy chaining along a finite adjacency path.
- Prototype, but do not yet commit to, adaptive joint mechanisms with mathlib's `Kernel.compProd`; identify the exact measurability and integration lemmas needed for approximate-DP composition.
- Test the proof rules on randomized response and on an abstract continuous probability measure.

Acceptance: post-processing and independent composition are proved from the event definition, and the adaptive-composition spike ends in either a checked proof prototype or a written list of missing lemmas. No composition property is installed as an axiom/typeclass field.

### Milestone 3 -- Continuous Laplace mechanism (first flagship milestone)

- Define the Laplace density and measure on `ℝ` with a strictly-positive scale in the primary constructor. If a total convenience constructor is later useful, specify its nonpositive-scale branch separately and never use that branch implicitly in a privacy theorem.
- Prove density nonnegativity, measurability, integral normalization, probability status, translation, and the pointwise density-ratio inequality.
- Define real-valued query sensitivity for a generic adjacency relation.
- Prove the standard scale `Δ/ε` theorem under `0 < ε` and an explicit sensitivity bound. Treat `ε = 0` separately: zero sensitivity implies adjacency-invariance of the query and hence 0-DP after adding any fixed noise; positive sensitivity has no finite `Δ/ε` calibration. Do not manufacture a theorem through Lean's division-by-zero convention.
- Add at least one vector/product extension or a clear theorem showing how an `L1` proof will compose.

Acceptance: a no-`sorry`, `#print axioms`-audited theorem for the scalar Laplace mechanism over Borel `ℝ`, plus regression examples at boundary parameters.

### Milestone 4 -- Approximate DP toolkit and Gaussian mechanism

- Define/prove useful hockey-stick divergence facts and density-based sufficient conditions.
- Prove the direct event-definition/hockey-stick equivalence with an unambiguous scale `γ = exp ε`.
- Complete adaptive sequential composition with explicit measurable continuations, proving the `(ε₁ + ε₂, δ₁ + δ₂)` bound from first principles using kernels/iterated integrals. Then add carefully stated parallel composition; it needs a database decomposition/disjoint-access hypothesis, not probabilistic independence alone.
- Develop Gaussian tail inequalities needed by the chosen calibration theorem.
- Reuse mathlib's `gaussianReal`; prove shifted-density/privacy-loss lemmas.
- Prove a standard scalar Gaussian mechanism theorem with its exact stated calibration and parameter side conditions.
- In a separate research spike, define continuous Rényi divergence first for `α > 1`, prove equality/self and the specific shifted-Gaussian formula, and inventory the general data-processing/product lemmas actually needed.
- Only after that spike succeeds, add RDP/zCDP definitions and conversions, borrowing SampCert's proof ideas only after generalizing every discrete sum argument to measures.

Acceptance: a theorem for a named, literature-cited Gaussian calibration whose Lean statement has been independently checked against the paper, plus numerical sanity checks outside the trusted proof layer.

### Milestone 5 -- Algorithm library and ergonomics

- Randomized response as a discrete regression test of the generic API.
- Report noisy max using continuous Laplace noise.
- Histogram/vector queries and standard adjacency/sensitivity lemmas.
- Exponential mechanism over a base measure, provided the utility is measurable and its normalizer is finite and nonzero. Make these hypotheses visible; arbitrary output spaces do not guarantee normalization.
- Proof combinators, simp lemmas, namespace discipline, tutorials, and generated API docs.
- Decide whether advanced composition, privacy amplification, Rényi DP, zCDP, or coupling rules should be the next extension based on user examples.

Acceptance: two nontrivial end-to-end algorithms, one continuous and compositional, can be proved without unfolding measure construction internals in user code.

## 5. Implementation difficulties and risks

### Fundamental mathematical/formalization difficulties

1. **Measurability is pervasive.** `map`, `bind`, parameterized measures, densities, and adaptive continuations all need the right measurable hypotheses. Hiding them can make definitions false or noncomposable; exposing all of them can make the API unusable.
2. **`ENNReal` arithmetic is subtle.** Coercions from `NNReal`/`Real`, `∞`, division by zero, and distributivity side conditions regularly dominate proofs. Prefer multiplication and finite probability bounds over division.
3. **Parameterized-law measurability.** It is not enough that every fixed Laplace law is a probability measure. Adaptive composition may need the map from its location/scale parameters into probability measures to be measurable.
4. **Density bounds to event bounds.** The standard paper step “integrate both sides” requires measurable nonnegative densities, restricted integrals, and careful `ae` reasoning.
5. **Radon--Nikodym side conditions.** Absolute continuity and available Lebesgue-decomposition instances must be explicit. Degenerate Gaussians/Dirac measures break naive density formulas.
6. **Approximate composition.** Direct event manipulations for bind require Tonelli-style arguments and measurable kernels. A divergence formulation may simplify this, but equivalence itself is substantial work.
7. **Gaussian calibration and tails.** Exact constants, parameter regimes, `log`/`sqrt` domains, and Gaussian tail theorems are error-prone and may expose gaps in mathlib.
8. **Higher-dimensional laws.** Mathlib's best-developed named Gaussian law is currently on `ℝ`; finite-dimensional multivariate mechanisms may require product constructions or additional Gaussian measure infrastructure.
9. **Boundary cases.** `ε = 0`, `δ = 0/1`, zero sensitivity, zero variance, nonpositive Laplace scale, and empty datasets need intentional semantics and tests.
10. **Adjacency conventions differ.** Add/remove and replace-one adjacency change sensitivities and constants. The theorem statement must never conceal which convention is used.
11. **Divergence conventions differ.** Rényi orders, logarithm bases, hockey-stick parameterization, max-divergence codomains, and behavior without absolute continuity vary across sources. Definitions need reference citations and boundary tests.

### Engineering and ecosystem difficulties

12. **Fast-moving dependencies.** Lean/mathlib releases can rename or generalize APIs. Exact pins and controlled upgrade PRs are essential.
13. **Compile time and import weight.** Pulling all measure theory into every file will slow iteration. Imports and module boundaries need regular profiling.
14. **Upstream API gaps.** Laplace distribution facts and some `measure.real` or kernel lemmas may be missing. Project-local lemmas should be isolated so they can later move upstream.
15. **Proof abstraction can overfit.** SampCert's abstract `DPSystem` is useful for its goals but assumes one additive parameter and approximate-DP conversion. A premature generalized privacy typeclass could make `(ε,δ)`, RDP, and zCDP awkward. Start with concrete relations, then extract interfaces from proven examples.
16. **No executable semantics.** This scope proves ideal mathematical mechanisms, not correctness or security of floating-point samplers. Documentation must state that boundary prominently.
17. **Discoverability.** Measure-theoretic proofs can become implementation-heavy. Stable façade lemmas and worked examples are part of correctness engineering, not optional polish.

### Soundness and code-reuse risks

18. **A compiling proof can formalize the wrong theorem.** Every flagship statement needs a plain-language restatement, a literature citation, and review of adjacency and parameter conventions.
19. **Imported code may rely on stronger hidden assumptions.** Before reuse, inspect imports, typeclass assumptions, axioms, `noncomputable` definitions, and degenerate branches.
20. **Version drift can invalidate audits.** Record source commits rather than links to moving `main` branches.
21. **Automation can hide brittle steps.** Avoid unexplained broad `aesop`/`simp` proofs in foundational inequalities; retain intermediate lemmas that expose mathematical reasoning.

## 6. Review and validation policy

For every imported or adapted result:

1. Record origin, commit/tag, license, and corresponding mathematical source.
2. Restate the claim independently and check units, adjacency, parameter domains, event measurability, and symmetry.
3. Read the full dependency chain relevant to the theorem; search for `axiom`, `sorry`, and unusual local instances.
4. Reprove small foundational claims directly when cheaper than trusting a complicated port.
5. Add adversarial boundary tests and at least one finite-model sanity check where probabilities can be calculated explicitly.
6. Run `#print axioms` on public headline theorems and keep the result limited to expected classical/choice/quotient foundations from Lean/mathlib.
7. Require a second human review for the formal theorem statement and another for the analytic proof of each flagship mechanism.

At the end of each mechanism milestone, add a composition round-trip example: define a concrete query, prove sensitivity, add noise, compose it with another mechanism, convert privacy notions if applicable, and check that the final symbolic bound agrees with a hand calculation. For equality/self lemmas of future divergences, test both ordinary probability measures and singular pairs so that `∞` conventions are exercised.

Numerical scripts may test constants and catch reversed inequalities, but they are not proof dependencies. Likewise, continuous mathematical privacy must not be advertised as an implementation guarantee for finite-precision sampling.

## 7. Recommended first development slice

Do not begin with a grand generalized privacy calculus. Implement this vertical slice:

1. `MeasureClose ε δ μ ν` over `ProbabilityMeasure` using measurable events.
2. `DifferentiallyPrivate adj M ε δ` for arbitrary input and measurable output types.
3. monotonicity, constants, deterministic post-processing, and pure-to-approximate DP;
4. scalar Laplace probability measure;
5. density domination for two shifted Laplace laws;
6. scalar Laplace mechanism privacy from sensitivity.

This slice tests nearly every decisive design choice—continuous events, `ENNReal`, measurability, density integration, parameter boundaries, adjacency, and user ergonomics—without the additional Gaussian-tail burden. Only after it is stable should adaptive bind and a broad abstract DP interface be finalized.

## 8. Decisions to revisit after the Laplace milestone

- Whether mechanisms should publicly be functions into `ProbabilityMeasure`, probability kernels, or a small wrapper supporting both.
- Whether approximate DP should use `(ε, δ)` as two arguments or a validated parameter structure.
- Whether hockey-stick divergence becomes the core definition or remains an equivalent proof interface.
- Whether generalized privacy notions deserve a SampCert-like typeclass, a graded relational structure, or ordinary theorem families.
- Which general results belong upstream in mathlib (most likely the Laplace distribution) versus in this DP package.

The conservative recommendation is to optimize first for transparent mathematical statements and dependable composition proofs, not executable notation or maximal abstraction.
