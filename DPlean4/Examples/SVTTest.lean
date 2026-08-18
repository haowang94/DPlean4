/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.SVT
import DPlean4.Basic.Adjacency

/-!
# Sparse Vector Technique Tests

End-to-end examples verifying the SVT mechanisms.
-/

namespace DPlean4

open scoped NNReal

section CountQuery

variable {α : Type*} [DecidableEq α]

/-- Count query has L1 sensitivity 1 under add/remove adjacency. -/
private theorem count_sensitivity :
    HasL1Sensitivity ListAddRemove (fun (l : List α) => (l.length : ℝ)) 1 := by
  intro l₁ l₂ hadj
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj <;> rw [h.1, h.2] <;>
    simp [List.length_cons] <;> norm_num

/-- Private threshold test on list count: is the count above T?
    ε-DP for any ε > 0. -/
theorem private_count_threshold (T : ℝ) (ε : NNReal) (hε : ε ≠ 0) :
    IsPureDP ListAddRemove
      (aboveThreshold (fun (l : List α) => (l.length : ℝ)) T 1 ε) ε :=
  aboveThreshold_isPureDP T hε count_sensitivity

/-- Private threshold test with shared threshold noise.
    ε-DP regardless of the threshold noise scale b_t. -/
theorem private_count_noisy_threshold (T : ℝ) (ε : NNReal) (b_t : NNReal) (hε : ε ≠ 0) :
    IsPureDP ListAddRemove
      (noisyAboveThreshold (fun (l : List α) => (l.length : ℝ)) T 1 ε b_t) ε :=
  noisyAboveThreshold_isPureDP T b_t hε count_sensitivity

end CountQuery

end DPlean4
