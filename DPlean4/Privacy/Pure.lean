/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Probability.Mechanism
import DPlean4.Privacy.MeasureClose

/-!
# Pure Differential Privacy

This file defines pure ε-differential privacy for mechanisms.

## Main Definitions

* `IsPureDP adj M ε`: Mechanism `M` satisfies pure ε-DP with respect to adjacency `adj`

## Key Properties

* Reflexivity: constant mechanisms are 0-DP
* Monotonicity in ε
* Closure under postprocessing (in separate file)
* Composition (in separate file)
-/

namespace DPlean4

open MeasureTheory

variable {D O : Type*} [MeasurableSpace O]

/-- A mechanism satisfies pure ε-differential privacy if for all adjacent databases,
the output distributions are ε-close in the pure sense (δ=0).

Adjacency is a relation parameter, not hardcoded. This allows the same mechanism
to be analyzed under different adjacency notions.
-/
def IsPureDP (adj : D → D → Prop) (M : Mechanism D O) (ε : NNReal) : Prop :=
  ∀ d₁ d₂, adj d₁ d₂ → PureMeasureClose ε (M d₁) (M d₂)

/-- A constant mechanism (always returns the same distribution) satisfies 0-DP
under any adjacency relation. -/
theorem constantMechanism_isPureDP {μ : ProbabilityMeasure O} (adj : D → D → Prop) :
    IsPureDP adj (fun (_ : D) => μ) 0 := by
  intro d₁ d₂ _
  exact pureMeasureClose_refl μ

/-- Pure DP is monotone in ε. -/
theorem isPureDP_mono {adj : D → D → Prop} {M : Mechanism D O} {ε₁ ε₂ : NNReal}
    (h : IsPureDP adj M ε₁) (hle : ε₁ ≤ ε₂) :
    IsPureDP adj M ε₂ := by
  intro d₁ d₂ hadj
  exact measureClose_epsilon_mono (h d₁ d₂ hadj) hle

/-- If adjacency is symmetric, then pure ε-DP is symmetric: μ ≤[ε] ν implies ν ≤[ε] μ
    requires the symmetric adjacency property. -/
theorem isPureDP_symm_of_adj_symm {adj : D → D → Prop} {M : Mechanism D O} {ε : NNReal}
    (hadj_symm : ∀ d₁ d₂, adj d₁ d₂ → adj d₂ d₁)
    (h : IsPureDP adj M ε) :
    ∀ d₁ d₂, adj d₁ d₂ → PureMeasureClose ε (M d₂) (M d₁) := by
  intro d₁ d₂ hadj
  exact h d₂ d₁ (hadj_symm d₁ d₂ hadj)

end DPlean4
