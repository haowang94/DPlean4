/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Exponential
import DPlean4.Basic.Adjacency

/-!
# Randomized Response Mechanism

This file implements the classic randomized response mechanism and proves it satisfies
differential privacy.

## Key Insight

Randomized response is a **special case of the exponential mechanism**. The utility
function is `u(d, o) = 1 if o = d, else 0` with sensitivity Δ = 1. The exponential
mechanism samples `o` with probability proportional to `exp(ε · u(d,o) / (2Δ))`:

  - P(output = input) ∝ exp(ε/2)
  - P(output ≠ input) ∝ 1

This gives ε-DP directly from `expMech_isPureDP`, eliminating the need for manual
discrete probability measure construction.

## Main Results

* `randomizedResponse_isPureDP`: Randomized response satisfies ε-DP (sorry-free)
-/

namespace DPlean4

open scoped NNReal

/-- Adjacency for single-bit databases: all pairs are adjacent.
    This models the worst case where any two inputs could be neighbors. -/
def SingleBitAdjacent : Bool → Bool → Prop := fun _ _ => True

/-- Utility function for randomized response: prefer outputting the true value.
    `rrUtility d o = 1` if `o = d` (correct output), `0` otherwise. -/
def rrUtility : Bool → Bool → ℝ := fun d o => if d = o then 1 else 0

/-- Changing the input bit changes the utility by at most 1. -/
theorem rrUtility_sensitivity :
    HasUtilitySensitivity SingleBitAdjacent rrUtility 1 := by
  intro d₁ d₂ _ o
  simp only [rrUtility]
  cases d₁ <;> cases d₂ <;> cases o <;> simp

/-- Randomized response as an exponential mechanism: samples the output bit
    with probability proportional to `exp(ε/2)` for the correct bit and `1`
    for the incorrect bit. -/
noncomputable def randomizedResponse (ε : NNReal) : Mechanism Bool Bool :=
  expMech rrUtility (ε : ℝ) 1

/-- **Randomized response satisfies ε-DP.**

    This follows immediately from the exponential mechanism theorem: the utility
    `u(d,o) = 1_{o=d}` has sensitivity 1, so the exponential mechanism is ε-DP.

    The mechanism outputs the true bit with probability `exp(ε/2)/(exp(ε/2) + 1)`
    and flips with probability `1/(exp(ε/2) + 1)`. -/
theorem randomizedResponse_isPureDP (ε : NNReal) :
    IsPureDP SingleBitAdjacent (randomizedResponse ε) ε :=
  expMech_isPureDP (by norm_num : (0 : ℝ) < 1) rrUtility_sensitivity

end DPlean4
