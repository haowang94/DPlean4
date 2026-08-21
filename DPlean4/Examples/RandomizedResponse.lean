/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Exponential
import DPlean4.Basic.Adjacency
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Randomized Response Mechanism

This file implements the classic randomized response mechanism (Warner, 1965) and
proves it satisfies ε-differential privacy with the standard, tight calibration.

## Calibration

Classic ε-randomized response reports the true bit with probability
`exp(ε)/(exp(ε)+1)` and flips it with probability `1/(exp(ε)+1)`. The privacy
loss on any output is exactly `ε`, so this is the tight ε-DP mechanism.

We build the two-point output distribution directly (as a normalized `PMF` over
`Bool`) and prove ε-DP by a direct likelihood-ratio bound, rather than routing
through the generic exponential-mechanism bound. That generic bound loses a
factor of two here: `expMech` with an indicator utility yields truth probability
`exp(ε/2)/(exp(ε/2)+1)`, i.e. it must add twice as much noise to certify the same
ε. The exp-mechanism version is kept below as `randomizedResponseExpMech` for
reference.

## Main Results

* `randomizedResponse_isPureDP`: classic randomized response satisfies ε-DP
* `randomizedResponseExpMech_isPureDP`: the (looser) exponential-mechanism variant
-/

noncomputable section

namespace DPlean4

open MeasureTheory ENNReal PMF
open scoped NNReal ENNReal

/-- Adjacency for single-bit databases: all pairs are adjacent.
    This models the worst case where any two inputs could be neighbors. -/
def SingleBitAdjacent : Bool → Bool → Prop := fun _ _ => True

-- ============================================================================
-- Classic randomized response (tight ε-calibration)
-- ============================================================================

/-- Unnormalized weight for classic randomized response: `exp ε` on the true bit
    `o = d`, and `1` on the flipped bit. Normalizing gives truth probability
    `exp ε / (exp ε + 1)`. -/
noncomputable def rrWeight (ε : ℝ) (d o : Bool) : ℝ≥0∞ :=
  if o = d then ENNReal.ofReal (Real.exp ε) else 1

theorem rrWeight_pos (ε : ℝ) (d o : Bool) : 0 < rrWeight ε d o := by
  simp only [rrWeight]; split_ifs
  · exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  · exact one_pos

theorem rrWeight_ne_top (ε : ℝ) (d o : Bool) : rrWeight ε d o ≠ ⊤ := by
  simp only [rrWeight]; split_ifs
  · exact ENNReal.ofReal_ne_top
  · exact one_ne_top

/-- The partition function is `exp ε + 1`, independent of the input bit. -/
theorem rrWeight_tsum (ε : ℝ) (d : Bool) :
    ∑' o, rrWeight ε d o = ENNReal.ofReal (Real.exp ε) + 1 := by
  rw [tsum_bool]
  cases d <;> simp [rrWeight, add_comm]

theorem rrWeight_tsum_ne_zero (ε : ℝ) (d : Bool) : ∑' o, rrWeight ε d o ≠ 0 := by
  rw [rrWeight_tsum]
  exact (lt_of_lt_of_le one_pos le_add_self).ne'

theorem rrWeight_tsum_ne_top (ε : ℝ) (d : Bool) : ∑' o, rrWeight ε d o ≠ ⊤ := by
  rw [rrWeight_tsum]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, one_ne_top⟩

/-- Classic randomized response PMF over `Bool`. -/
noncomputable def rrPMF (ε : ℝ) (d : Bool) : PMF Bool :=
  PMF.normalize (rrWeight ε d) (rrWeight_tsum_ne_zero ε d) (rrWeight_tsum_ne_top ε d)

/-- **Classic randomized response** as a `Mechanism Bool Bool`: report the true
    bit with probability `exp ε / (exp ε + 1)`, flip it otherwise. -/
noncomputable def randomizedResponse (ε : NNReal) : Mechanism Bool Bool :=
  fun d => ⟨(rrPMF (ε : ℝ) d).toMeasure, inferInstance⟩

@[simp]
theorem randomizedResponse_toMeasure (ε : NNReal) (d : Bool) :
    (randomizedResponse ε d).toMeasure = (rrPMF (ε : ℝ) d).toMeasure := rfl

/-- Pointwise weight bound: any weight for `d₁` is at most `exp ε` times the
    corresponding weight for `d₂`. Uses `exp ε ≥ 1` and every weight `≥ 1`. -/
theorem rrWeight_le (ε : ℝ) (hε : 0 ≤ ε) (d₁ d₂ o : Bool) :
    rrWeight ε d₁ o ≤ ENNReal.ofReal (Real.exp ε) * rrWeight ε d₂ o := by
  have he1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp ε) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hε)
  have hw2 : (1 : ℝ≥0∞) ≤ rrWeight ε d₂ o := by
    simp only [rrWeight]; split_ifs; exacts [he1, le_refl 1]
  have hw1 : rrWeight ε d₁ o ≤ ENNReal.ofReal (Real.exp ε) := by
    simp only [rrWeight]; split_ifs; exacts [le_refl _, he1]
  calc rrWeight ε d₁ o
      ≤ ENNReal.ofReal (Real.exp ε) := hw1
    _ = ENNReal.ofReal (Real.exp ε) * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal (Real.exp ε) * rrWeight ε d₂ o := by gcongr

/-- Pointwise PMF bound: `p(o|d₁) ≤ exp ε · p(o|d₂)`. The partition function is
    the same for both inputs, so this reduces to the weight bound. -/
theorem rrPMF_le (ε : ℝ) (hε : 0 ≤ ε) (d₁ d₂ o : Bool) :
    rrPMF ε d₁ o ≤ ENNReal.ofReal (Real.exp ε) * rrPMF ε d₂ o := by
  simp only [rrPMF, PMF.normalize_apply]
  rw [rrWeight_tsum ε d₁, rrWeight_tsum ε d₂]
  set Z := ENNReal.ofReal (Real.exp ε) + 1
  rw [show ENNReal.ofReal (Real.exp ε) * (rrWeight ε d₂ o * Z⁻¹)
        = (ENNReal.ofReal (Real.exp ε) * rrWeight ε d₂ o) * Z⁻¹ from by ring]
  gcongr
  exact rrWeight_le ε hε d₁ d₂ o

/-- **Classic randomized response satisfies ε-DP.**

    Both inputs induce the same partition function `exp ε + 1`, and every
    likelihood ratio is at most `exp ε`, so the mechanism is ε-DP with the tight
    calibration (truth probability `exp ε / (exp ε + 1)`). -/
theorem randomizedResponse_isPureDP (ε : NNReal) :
    IsPureDP SingleBitAdjacent (randomizedResponse ε) ε := by
  intro d₁ d₂ _ s _hs
  simp only [randomizedResponse_toMeasure, ENNReal.coe_zero, add_zero]
  rw [PMF.toMeasure_apply_eq_tsum _ s, PMF.toMeasure_apply_eq_tsum _ s,
      ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  simp only [Set.indicator]
  split_ifs
  · exact rrPMF_le (ε : ℝ) ε.coe_nonneg d₁ d₂ x
  · exact bot_le

-- ============================================================================
-- Exponential-mechanism variant (reference; looser ε/2 calibration)
-- ============================================================================

/-- Utility function for the exponential-mechanism variant: prefer outputting the
    true value. `rrUtility d o = 1` if `o = d`, `0` otherwise. -/
def rrUtility : Bool → Bool → ℝ := fun d o => if d = o then 1 else 0

/-- Changing the input bit changes the utility by at most 1. -/
theorem rrUtility_sensitivity :
    HasUtilitySensitivity SingleBitAdjacent rrUtility 1 := by
  intro d₁ d₂ _ o
  simp only [rrUtility]
  cases d₁ <;> cases d₂ <;> cases o <;> simp

/-- Randomized response realized as an exponential mechanism. This is the same
    family of mechanisms but with the *looser* calibration: to certify ε-DP it
    reports the true bit only with probability `exp(ε/2)/(exp(ε/2)+1)`. Prefer
    `randomizedResponse` for the tight classic calibration. -/
noncomputable def randomizedResponseExpMech (ε : NNReal) : Mechanism Bool Bool :=
  expMech rrUtility (ε : ℝ) 1

/-- The exponential-mechanism variant satisfies ε-DP (loosely calibrated). -/
theorem randomizedResponseExpMech_isPureDP (ε : NNReal) :
    IsPureDP SingleBitAdjacent (randomizedResponseExpMech ε) ε :=
  expMech_isPureDP one_ne_zero rrUtility_sensitivity

end DPlean4

end -- noncomputable section
