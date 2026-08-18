/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Probability.Mechanism
import DPlean4.Privacy.MeasureClose
import DPlean4.Privacy.Pure

/-!
# Approximate Differential Privacy

This file defines (ε,δ)-approximate differential privacy for mechanisms.

## Main Definitions

* `IsApproxDP adj M ε δ`: Mechanism `M` satisfies (ε,δ)-DP with respect to adjacency `adj`

## Key Properties

* Pure DP implies approximate DP (with δ=0)
* Monotonicity in both ε and δ
* Closure under postprocessing (in separate file)
* Composition (in separate file)
-/

namespace DPlean4

open MeasureTheory

variable {D O : Type*} [MeasurableSpace O]

/-- A mechanism satisfies (ε,δ)-approximate differential privacy if for all adjacent
databases, the output distributions are (ε,δ)-close.

The approximation parameter δ allows for a small probability of privacy failure.
-/
def IsApproxDP (adj : D → D → Prop) (M : Mechanism D O) (ε δ : NNReal) : Prop :=
  ∀ d₁ d₂, adj d₁ d₂ → MeasureClose ε δ (M d₁) (M d₂)

/-- Pure ε-DP implies (ε,δ)-DP for any δ. -/
theorem isApproxDP_of_isPureDP {adj : D → D → Prop} {M : Mechanism D O} {ε : NNReal} (δ : NNReal)
    (h : IsPureDP adj M ε) :
    IsApproxDP adj M ε δ := by
  intro d₁ d₂ hadj
  exact pureMeasureClose_to_measureClose δ (h d₁ d₂ hadj)

/-- A constant mechanism satisfies (0,0)-DP. -/
theorem constantMechanism_isApproxDP {μ : ProbabilityMeasure O} (adj : D → D → Prop) :
    IsApproxDP adj (fun (_ : D) => μ) 0 0 := by
  intro d₁ d₂ _
  exact measureClose_refl μ

/-- Approximate DP is monotone in ε. -/
theorem isApproxDP_epsilon_mono {adj : D → D → Prop} {M : Mechanism D O} {ε₁ ε₂ δ : NNReal}
    (h : IsApproxDP adj M ε₁ δ) (hle : ε₁ ≤ ε₂) :
    IsApproxDP adj M ε₂ δ := by
  intro d₁ d₂ hadj
  exact measureClose_epsilon_mono (h d₁ d₂ hadj) hle

/-- Approximate DP is monotone in δ. -/
theorem isApproxDP_delta_mono {adj : D → D → Prop} {M : Mechanism D O} {ε : NNReal} {δ₁ δ₂ : NNReal}
    (h : IsApproxDP adj M ε δ₁) (hle : δ₁ ≤ δ₂) :
    IsApproxDP adj M ε δ₂ := by
  intro d₁ d₂ hadj
  exact measureClose_delta_mono (h d₁ d₂ hadj) hle

/-- Setting δ=0 in approximate DP gives pure DP. -/
theorem isApproxDP_zero_iff_isPureDP {adj : D → D → Prop} {M : Mechanism D O} {ε : NNReal} :
    IsApproxDP adj M ε 0 ↔ IsPureDP adj M ε := by
  constructor
  · intro h; exact h
  · intro h; exact h

end DPlean4
