/-
Copyright (c) 2026 abobreshov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: abobreshov
-/

import LeanPool.MovingSofaEssay.Problem
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Moving Sofa Essay

Source: arxiv:1606.08111
Authors: abobreshov
Status: verified
Main declarations: `MovingSofaEssay.hammersley_area_bounds`, `MovingSofaEssay.unitSquare_movable`
Tags: moving-sofa, real-arithmetic
MSC: 52A40
-/

/-!
## Mathematical overview

The arithmetic behind a popular essay on the moving sofa problem, with the geometry
certified numerically elsewhere. These results simplify and bound Hammersley's area,
compute the top-wall excess after enlargement, and compare areas given an external
lower enclosure for Gerver's area. They do not formalize the geometric constructions
or verify the external numerical certificate.
-/

namespace MovingSofaEssay

open Real

/-- The area expression from Hammersley's rectangle and disc decomposition simplifies
to its published closed form; the geometric decomposition is supplied externally. -/
theorem hammersley_area_identity :
    4 / π + π / 2 - 2 / π = π / 2 + 2 / π := by
  ring

/-- Six-decimal bounds on π enclose Hammersley's closed-form area. -/
theorem hammersley_area_bounds :
    2.207415 < π / 2 + 2 / π ∧ π / 2 + 2 / π < 2.207417 := by
  have lower : (2 : ℝ) / 3.141593 < 2 / π := by
    apply (div_lt_div_iff₀ (by norm_num) pi_pos).2
    linarith [pi_lt_d6]
  have upper : 2 / π < (2 : ℝ) / 3.141592 := by
    apply (div_lt_div_iff₀ pi_pos (by norm_num)).2
    linarith [pi_gt_d6]
  constructor <;> linarith [pi_gt_d6, pi_lt_d6]

/-- Scaling a height-one sofa by 1.001 about height 1/2 raises its top above
the height-one wall by exactly 0.0005. -/
theorem enlargement_top_exceeds_wall :
    (1 / 2 + 1.001 * (1 / 2) - 1 : ℝ) = 0.0005 ∧
      0 < (1 / 2 + 1.001 * (1 / 2) - 1 : ℝ) := by
  norm_num

/-- Given the externally certified lower enclosure for Gerver's area, it strictly
exceeds Hammersley's area. The numerical enclosure is a hypothesis here. -/
theorem gerver_exceeds_hammersley (A : ℝ) (lower : 2.2195315 ≤ A) :
    π / 2 + 2 / π < A := by
  linarith [hammersley_area_bounds.2]

end MovingSofaEssay
