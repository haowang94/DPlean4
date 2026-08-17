/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Measure Closeness for Differential Privacy

This file defines the one-way approximate-DP relation between probability measures.

## Main Definitions

* `MeasureClose ε δ μ ν`: The one-way (ε,δ)-closeness relation via measurable events
* `PureMeasureClose ε μ ν`: Pure ε-closeness (δ=0 case)

## Design Notes

This is the **primary** definition of differential privacy at the measure level.
We define DP via the standard measurable-event inequality:

```
∀ s : Set O, MeasurableSet s → μ(s) ≤ exp(ε) * ν(s) + δ
```

**Not** via divergences. Divergences (hockey-stick, max, Rényi) are built as
equivalent characterizations *after* this event-based API works.

### Why events first?

1. **Standard definition**: Direct from textbooks (Dwork & Roth)
2. **Easy to audit**: No premature commitment to ENNReal/EReal/ℝ choices
3. **Avoids division**: Multiplicative form sidesteps ∞/0 issues

### Parameter choices

* `ε δ : NNReal` - non-negative reals, coerced to `ENNReal` in inequalities
* Do NOT build `δ ≤ 1` into the core relation - remains meaningful for all δ ≥ 0
* Separate `ValidDPParams` predicate for user-facing guarantees

### One-way vs symmetric

We define the *one-way* comparison `μ ≤[ε,δ] ν`. The full DP definition for mechanisms
applies this to both directions when adjacency is symmetric.
-/

namespace DPlean4

open MeasureTheory

variable {O : Type*} [MeasurableSpace O]

/-- Two probability measures are (ε,δ)-close in the one-way sense if for every
measurable event, the probability under μ is at most exp(ε) times the probability
under ν, plus δ.

This is the standard approximate-DP inequality at the measure level.
-/
def MeasureClose (ε δ : NNReal) (μ ν : ProbabilityMeasure O) : Prop :=
  ∀ s : Set O, MeasurableSet s →
    μ.toMeasure s ≤ ENNReal.ofReal (Real.exp ε) * ν.toMeasure s + (δ : ENNReal)

/-- Pure ε-closeness is (ε,0)-closeness: the approximation parameter δ is zero. -/
def PureMeasureClose (ε : NNReal) (μ ν : ProbabilityMeasure O) : Prop :=
  MeasureClose ε 0 μ ν

notation:50 μ " ≤[" ε "," δ "] " ν => MeasureClose ε δ μ ν
notation:50 μ " ≤[" ε "] " ν => PureMeasureClose ε μ ν

/-- `MeasureClose` is reflexive at (0,0): any measure is (0,0)-close to itself. -/
theorem measureClose_refl (μ : ProbabilityMeasure O) : μ ≤[0, 0] μ := by
  intro s _
  simp [Real.exp_zero]

/-- `PureMeasureClose` is reflexive at 0. -/
theorem pureMeasureClose_refl (μ : ProbabilityMeasure O) : μ ≤[0] μ :=
  measureClose_refl μ

/-- `MeasureClose` is monotone in ε: if μ ≤[ε₁,δ] ν and ε₁ ≤ ε₂, then μ ≤[ε₂,δ] ν. -/
theorem measureClose_epsilon_mono {ε₁ ε₂ δ : NNReal} {μ ν : ProbabilityMeasure O}
    (h : μ ≤[ε₁,δ] ν) (hle : ε₁ ≤ ε₂) : μ ≤[ε₂,δ] ν := by
  intro s hs
  exact le_trans (h s hs) (by gcongr)

/-- `MeasureClose` is monotone in δ: if μ ≤[ε,δ₁] ν and δ₁ ≤ δ₂, then μ ≤[ε,δ₂] ν. -/
theorem measureClose_delta_mono {ε : NNReal} {δ₁ δ₂ : NNReal} {μ ν : ProbabilityMeasure O}
    (h : μ ≤[ε,δ₁] ν) (hle : δ₁ ≤ δ₂) : μ ≤[ε,δ₂] ν := by
  intro s hs
  exact le_trans (h s hs) (by gcongr)

/-- Pure ε-closeness implies (ε,δ)-closeness for any δ. -/
theorem pureMeasureClose_to_measureClose {ε : NNReal} (δ : NNReal) {μ ν : ProbabilityMeasure O}
    (h : μ ≤[ε] ν) : μ ≤[ε, δ] ν := by
  intro s hs
  calc
    μ.toMeasure s
      ≤ ENNReal.ofReal (Real.exp ε) * ν.toMeasure s + (0 : ENNReal) := h s hs
    _ = ENNReal.ofReal (Real.exp ε) * ν.toMeasure s := by simp
    _ ≤ ENNReal.ofReal (Real.exp ε) * ν.toMeasure s + (δ : ENNReal) := le_self_add

/-- A constant mechanism (always returns the same measure) is (0,0)-close to itself
applied to any two inputs. -/
theorem constantMeasure_close (μ : ProbabilityMeasure O) :
    μ ≤[0, 0] μ :=
  measureClose_refl μ

end DPlean4
