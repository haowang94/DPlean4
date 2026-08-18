/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Exponential
import DPlean4.Basic.Sensitivity

/-!
# Report Noisy Max / Private Argmax Mechanism

The Report Noisy Max mechanism (Dwork & Roth, 2014, Section 3.3) privately selects
the index with highest query value. Given n queries `q₀,...,qₙ₋₁ : D → ℝ`, each
with sensitivity Δ, it outputs the index i that approximately maximizes `qᵢ(d)`.

## Key Insight

Report Noisy Max is a **special case of the exponential mechanism**: the utility
function `u(d, i) = qᵢ(d)` has sensitivity Δ whenever each individual query does.
This gives ε-DP directly from `expMech_isPureDP`, which is much tighter than the
naive nε bound from n-fold composition + argmax postprocessing.

## Main Results

* `reportNoisyMax_isPureDP`: Report Noisy Max satisfies ε-DP

## References

* Dwork & Roth, "The Algorithmic Foundations of Differential Privacy" (2014),
  Section 3.3, Algorithm 2 (Report Noisy Max)
* McSherry & Talwar, "Mechanism Design via Differential Privacy" (2007)
-/

noncomputable section

namespace DPlean4

open scoped NNReal ENNReal

variable {D : Type*} {n : ℕ}

-- ============================================================================
-- Query Utility
-- ============================================================================

/-- Build an exponential mechanism utility from a collection of queries:
    `queryUtility qs d i = qᵢ(d)`. -/
def queryUtility (qs : Fin n → D → ℝ) : D → Fin n → ℝ :=
  fun d i => qs i d

/-- If each query has L1 sensitivity at most Δ, then the query-evaluation utility
    has utility sensitivity Δ: changing the database changes any query's value
    by at most Δ. -/
theorem queryUtility_sensitivity {adj : D → D → Prop} {qs : Fin n → D → ℝ} {Δ : ℝ}
    (hsens : ∀ i, HasL1Sensitivity adj (qs i) Δ) :
    HasUtilitySensitivity adj (queryUtility qs) Δ := by
  intro d₁ d₂ hadj i
  exact hsens i d₁ d₂ hadj

-- ============================================================================
-- Report Noisy Max
-- ============================================================================

variable [Nonempty (Fin n)]

/-- The Report Noisy Max mechanism: given n queries, privately select the index
    with highest value by running the exponential mechanism with utility
    `u(d, i) = qᵢ(d)`.

    Samples index i with probability proportional to `exp(ε · qᵢ(d) / (2Δ))`,
    favoring indices with higher query values. -/
def reportNoisyMax (qs : Fin n → D → ℝ) (ε : NNReal) (Δ : ℝ) :
    Mechanism D (Fin n) :=
  expMech (queryUtility qs) ε Δ

/-- **Report Noisy Max satisfies ε-DP.**

    If each of the n queries has L1 sensitivity at most Δ > 0 under adjacency `adj`,
    then the Report Noisy Max mechanism satisfies ε-DP. The bound is ε (not nε)
    because it uses the exponential mechanism analysis, not naive composition.

    This is Algorithm 2 from Dwork & Roth (2014), Section 3.3. -/
theorem reportNoisyMax_isPureDP {adj : D → D → Prop}
    {qs : Fin n → D → ℝ} {Δ : ℝ} (hΔ : 0 < Δ) {ε : NNReal}
    (hsens : ∀ i, HasL1Sensitivity adj (qs i) Δ) :
    IsPureDP adj (reportNoisyMax qs ε Δ) ε :=
  expMech_isPureDP hΔ (queryUtility_sensitivity hsens)

end DPlean4

end -- noncomputable section
