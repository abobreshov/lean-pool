/-
Copyright (c) 2026 abobreshov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: abobreshov
-/

import LeanPool.MovingSofaEssay.Problem
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FunProp

/-!
# Hammersley's sofa and its circular-centre motion

AIH-25 defines the rectangle and two quarter discs with an open semicircular
notch removed. The set is measurable and bounded, and sufficiently far horizontal
and vertical translations fit their respective hallway arms.

The proposed rotation about a stationary notch centre at the origin does not fit:
already at angle zero, the rightmost point has x-coordinate 1 + 2/π > 1.
This refutes the round-1 motion. The corrected round-2 motion moves the notch
centre on a circle about the inner corner during the turn and proves movability.
The area calculation is outside this geometric formalization.
-/

namespace MovingSofaEssay

open Real

/-- The rectangle between two unit quarter discs, with the open radius-2/π
disc removed. All points of the outer shape have nonnegative second coordinate. -/
noncomputable def hammersleySofa : Set (ℝ × ℝ) :=
  ((Set.Icc (-(2 / π)) (2 / π) ×ˢ Set.Icc 0 1) ∪
    {p | (p.1 + 2 / π) ^ 2 + p.2 ^ 2 ≤ 1 ∧ p.1 ≤ -(2 / π) ∧ 0 ≤ p.2} ∪
    {p | (p.1 - 2 / π) ^ 2 + p.2 ^ 2 ≤ 1 ∧ 2 / π ≤ p.1 ∧ 0 ≤ p.2}) \
    {p | p.1 ^ 2 + p.2 ^ 2 < (2 / π) ^ 2}

/-- The outer pieces are closed, and removing the open notch preserves closedness. -/
theorem hammersleySofa_closed : IsClosed hammersleySofa := by
  unfold hammersleySofa
  apply IsClosed.sdiff
  · apply IsClosed.union
    · apply IsClosed.union
      · exact isClosed_Icc.prod isClosed_Icc
      · exact (isClosed_le
          (f := fun p : ℝ × ℝ ↦ (p.1 + 2 / π) ^ 2 + p.2 ^ 2)
          (by fun_prop) continuous_const).inter
          ((isClosed_le continuous_fst continuous_const).inter
            (isClosed_le continuous_const continuous_snd))
    · exact (isClosed_le
        (f := fun p : ℝ × ℝ ↦ (p.1 - 2 / π) ^ 2 + p.2 ^ 2)
        (by fun_prop) continuous_const).inter
        ((isClosed_le continuous_const continuous_fst).inter
          (isClosed_le continuous_const continuous_snd))
  · exact isOpen_lt (by fun_prop) continuous_const

/-- Hammersley's sofa is Lebesgue measurable because it is closed. -/
theorem hammersleySofa_measurable : MeasurableSet hammersleySofa :=
  hammersleySofa_closed.measurableSet

/-- The sofa lies in its width-2(1 + 2/π), height-one bounding rectangle. -/
theorem hammersleySofa_subset_box :
    hammersleySofa ⊆ Set.Icc (-(1 + 2 / π)) (1 + 2 / π) ×ˢ Set.Icc 0 1 := by
  intro p hp
  have radius : 0 < 2 / π := div_pos (by norm_num) pi_pos
  rcases hp.1 with (rectangle | left) | right
  · exact ⟨⟨by linarith [rectangle.1.1], by linarith [rectangle.1.2]⟩, rectangle.2⟩
  · refine ⟨⟨?_, ?_⟩, left.2.2, ?_⟩
    · nlinarith [left.1, sq_nonneg p.2, sq_nonneg (p.1 + 2 / π + 1)]
    · linarith [left.2.1]
    · nlinarith [left.1, sq_nonneg (p.1 + 2 / π), sq_nonneg (p.2 - 1)]
  · refine ⟨⟨?_, ?_⟩, right.2.2, ?_⟩
    · linarith [right.2.1]
    · nlinarith [right.1, sq_nonneg p.2, sq_nonneg (p.1 - 2 / π - 1)]
    · nlinarith [right.1, sq_nonneg (p.1 - 2 / π), sq_nonneg (p.2 - 1)]

/-- The sofa is bounded as a subset of a bounded product of real intervals. -/
theorem hammersleySofa_bounded : Bornology.IsBounded hammersleySofa :=
  ((Metric.isBounded_Icc _ _).prod (Metric.isBounded_Icc _ _)).subset
    hammersleySofa_subset_box

/-- A left translation by at least 2/π places the sofa in the horizontal arm. -/
theorem hammersleySofa_horizontal {d : ℝ} (hd : 2 / π ≤ d) :
    (rigid 0 (-d, 0)) '' hammersleySofa ⊆
      {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
  rintro p ⟨q, hq, rfl⟩
  have bounds := hammersleySofa_subset_box hq
  simp only [rigid, cos_zero, sin_zero, one_mul, zero_mul, sub_zero, zero_add,
    add_zero, Set.mem_setOf_eq]
  exact ⟨by linarith [bounds.1.2], bounds.2⟩

/-- A quarter-turn followed by downward translation by at least 2/π fits the vertical arm. -/
theorem hammersleySofa_vertical {d : ℝ} (hd : 2 / π ≤ d) :
    (rigid (-(π / 2)) (0, -d)) '' hammersleySofa ⊆
      {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1} := by
  rintro p ⟨q, hq, rfl⟩
  have bounds := hammersleySofa_subset_box hq
  norm_num [rigid] at ⊢
  exact ⟨bounds.2.1, bounds.2.2, by linarith [bounds.1.1]⟩

/-- Translating left by 1 + 2/π meets the required far-horizontal start condition. -/
theorem hammersleySofa_start :
    (rigid 0 (-(1 + 2 / π), 0)) '' hammersleySofa ⊆
      {p | p.1 ≤ 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
  rintro p ⟨q, hq, rfl⟩
  have bounds := hammersleySofa_subset_box hq
  norm_num [rigid]
  exact ⟨by linarith [bounds.1.2], bounds.2⟩

/-- After a quarter-turn, translating down by 1 + 2/π meets the far-vertical end condition. -/
theorem hammersleySofa_finish :
    (rigid (-(π / 2)) (0, -(1 + 2 / π))) '' hammersleySofa ⊆
      {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 0} := by
  rintro p ⟨q, hq, rfl⟩
  have bounds := hammersleySofa_subset_box hq
  norm_num [rigid]
  exact ⟨bounds.2.1, bounds.2.2, by linarith [bounds.1.1]⟩

/-- The rightmost quarter-disc endpoint survives removal of the open notch. -/
theorem hammersleySofa_rightmost_mem : (1 + 2 / π, 0) ∈ hammersleySofa := by
  have radius : 0 < 2 / π := div_pos (by norm_num) pi_pos
  refine ⟨Or.inr ?_, ?_⟩
  · norm_num
  · dsimp
    nlinarith

/-- The prescribed stationary-centre turn fails at angle zero: its rightmost
point has x-coordinate 1 + 2/π, exceeding the hallway's outer wall at x = 1. -/
theorem hammersleySofa_origin_obstruction :
    ¬ (rigid 0 (0, 0)) '' hammersleySofa ⊆ hallway := by
  intro containment
  have point := containment (Set.mem_image_of_mem _ hammersleySofa_rightmost_mem)
  have radius : 0 < 2 / π := div_pos (by norm_num) pi_pos
  norm_num [rigid, hallway] at point
  rcases point with horizontal | vertical <;> linarith

/-- Rotation about the fixed notch centre cannot provide the phase-two containment
required in the round-1 brief. This does not rule out other motions of the same sofa. -/
theorem hammersleySofa_stationary_turn_impossible :
    ¬ ∀ α ∈ Set.Icc (0 : ℝ) (π / 2),
      (rigid (-α) (0, 0)) '' hammersleySofa ⊆ hallway := by
  intro turn
  have initial := turn 0 ⟨le_rfl, by positivity⟩
  exact hammersleySofa_origin_obstruction (by simpa using initial)

/-- The refuted round-1 angle, with a stationary orientation before and after the turn. -/
noncomputable def refutedRoundOneHammersleyAngle (t : ℝ) : ℝ :=
  -(π / 2 * min (max (3 * t - 1) 0) 1)

/-- The refuted round-1 translation places the notch centre at the origin throughout the turn.
It is continuous but does not keep the sofa inside the hallway. -/
noncomputable def refutedRoundOneHammersleyTranslation (t : ℝ) : ℝ × ℝ :=
  ((1 + 2 / π) * (min (3 * t) 1 - 1), -(1 + 2 / π) * max (3 * t - 2) 0)

/-- Both paths prescribed in the round-1 brief are continuous everywhere on ℝ. -/
theorem proposedHammersleyMotion_continuous :
    Continuous refutedRoundOneHammersleyAngle ∧
      Continuous refutedRoundOneHammersleyTranslation := by
  constructor
  · unfold refutedRoundOneHammersleyAngle
    continuity
  · unfold refutedRoundOneHammersleyTranslation
    continuity

/-- The proposed path meets both far-arm endpoint conditions, despite failing in between. -/
theorem proposedHammersleyMotion_endpoints :
    (rigid (refutedRoundOneHammersleyAngle 0) (refutedRoundOneHammersleyTranslation 0)) ''
        hammersleySofa ⊆ {p | p.1 ≤ 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} ∧
    (rigid (refutedRoundOneHammersleyAngle 1) (refutedRoundOneHammersleyTranslation 1)) ''
        hammersleySofa ⊆ {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 0} := by
  constructor
  · convert hammersleySofa_start using 1
    norm_num [refutedRoundOneHammersleyAngle, refutedRoundOneHammersleyTranslation]
  · convert hammersleySofa_finish using 1
    norm_num [refutedRoundOneHammersleyAngle, refutedRoundOneHammersleyTranslation]

/-- At time 1/3 the notch centre reaches the origin and the rightmost endpoint
crosses the outer wall. Thus this continuous path is not a witness of movability. -/
theorem proposedHammersleyMotion_fails :
    ¬ (rigid (refutedRoundOneHammersleyAngle (1 / 3))
      (refutedRoundOneHammersleyTranslation (1 / 3))) '' hammersleySofa ⊆ hallway := by
  convert hammersleySofa_origin_obstruction using 1
  norm_num [refutedRoundOneHammersleyAngle, refutedRoundOneHammersleyTranslation]

private theorem unit_disc_projection {a b c s : ℝ}
    (hab : a ^ 2 + b ^ 2 ≤ 1) (hcs : c ^ 2 + s ^ 2 = 1) : a * c + b * s ≤ 1 := by
  have identity : (a * c + b * s) ^ 2 + (a * s - b * c) ^ 2 =
      (a ^ 2 + b ^ 2) * (c ^ 2 + s ^ 2) := by ring
  rw [hcs, mul_one] at identity
  nlinarith [sq_nonneg (a * s - b * c), sq_nonneg (a * c + b * s - 1)]

private theorem notch_avoids_inner_corner {r u v c s : ℝ}
    (hv : 0 ≤ v) (hn : r ^ 2 ≤ u ^ 2 + v ^ 2)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1) :
    0 ≤ (u - r) * c + v * s ∨ 0 ≤ -(u + r) * s + v * c := by
  by_contra! outside
  let a := -((u - r) * c + v * s)
  let b := -(-(u + r) * s + v * c)
  have ha : 0 < a := by dsimp [a]; linarith [outside.1]
  have hb : 0 < b := by dsimp [b]; linarith [outside.2]
  have height : a * s + b * c + v = 2 * r * s * c := by
    calc
      _ = 2 * r * s * c + v * (1 - (c ^ 2 + s ^ 2)) := by dsimp [a, b]; ring
      _ = _ := by rw [hcs]; ring
  have sine : 0 < s := by
    by_contra h
    have zero : s = 0 := le_antisymm (le_of_not_gt h) hs
    have cosine : 0 < c := by nlinarith [hcs]
    rw [zero] at height
    nlinarith [mul_pos hb cosine]
  have cosine : 0 < c := by
    by_contra h
    have zero : c = 0 := le_antisymm (le_of_not_gt h) hc
    rw [zero] at height
    nlinarith [mul_pos ha sine]
  have bound_a : a < 2 * r * c := by
    apply (mul_lt_mul_iff_left₀ sine).mp
    nlinarith [mul_pos hb cosine]
  have bound_b : b < 2 * r * s := by
    apply (mul_lt_mul_iff_left₀ cosine).mp
    nlinarith [mul_pos ha sine]
  have norm : u ^ 2 + v ^ 2 = (r * c - a) ^ 2 + (r * s - b) ^ 2 := by
    calc
      _ = (u ^ 2 + v ^ 2) * (c ^ 2 + s ^ 2) := by rw [hcs, mul_one]
      _ = _ := by dsimp [a, b]; ring
  nlinarith [mul_pos ha (sub_pos.mpr bound_a), mul_pos hb (sub_pos.mpr bound_b),
    congrArg (fun z : ℝ ↦ r ^ 2 * z) hcs]

/-- Moving the notch centre on the radius-2/π circle keeps the sofa inside
the hallway throughout the clockwise quarter-turn. -/
theorem hammersleySofa_turn {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) (π / 2)) :
    (rigid (-α) (-(2 / π) * cos α, -(2 / π) * sin α)) '' hammersleySofa ⊆ hallway := by
  rintro p ⟨q, hq, rfl⟩
  have bounds := hammersleySofa_subset_box hq
  have radius : 0 < 2 / π := div_pos (by norm_num) pi_pos
  have hc : 0 ≤ cos α := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, hα.1], hα.2⟩
  have hs : 0 ≤ sin α := sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [pi_pos, hα.2])
  have unit : cos α ^ 2 + sin α ^ 2 = 1 := by linarith [sin_sq_add_cos_sq α]
  have vs : q.2 * sin α ≤ 1 := by
    have bound := mul_le_mul_of_nonneg_right bounds.2.2 hs
    nlinarith [sin_le_one α]
  have vc : q.2 * cos α ≤ 1 := by
    have bound := mul_le_mul_of_nonneg_right bounds.2.2 hc
    nlinarith [cos_le_one α]
  have upper : (q.1 - 2 / π) * cos α + q.2 * sin α ≤ 1 ∧
      -(q.1 + 2 / π) * sin α + q.2 * cos α ≤ 1 := by
    rcases hq.1 with (rectangle | left) | right
    · constructor
      · nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr rectangle.1.2) hc]
      · have negative : -(q.1 + 2 / π) ≤ 0 := by linarith [rectangle.1.1]
        nlinarith [mul_nonpos_of_nonpos_of_nonneg negative hs]
    · constructor
      · have negative : q.1 - 2 / π ≤ 0 := by linarith [left.2.1]
        nlinarith [mul_nonpos_of_nonpos_of_nonneg negative hc]
      · apply unit_disc_projection (b := q.2)
        · nlinarith [left.1]
        · linarith [unit]
    · constructor
      · exact unit_disc_projection right.1 unit
      · have negative : -(q.1 + 2 / π) ≤ 0 := by linarith [right.2.1]
        nlinarith [mul_nonpos_of_nonpos_of_nonneg negative hs]
  have corner := notch_avoids_inner_corner bounds.2.1 (le_of_not_gt hq.2) hc hs unit
  have pose : rigid (-α) (-(2 / π) * cos α, -(2 / π) * sin α) q =
      ((q.1 - 2 / π) * cos α + q.2 * sin α,
        -(q.1 + 2 / π) * sin α + q.2 * cos α) := by
    ext <;> simp [rigid, cos_neg, sin_neg] <;> ring
  rw [pose]
  rcases corner with horizontal | vertical
  · exact Or.inr ⟨horizontal, upper.1, upper.2⟩
  · exact Or.inl ⟨upper.1, vertical, upper.2⟩

/-- The positive turn parameter, clamped to [0, π/2] outside the middle phase. -/
noncomputable def hammersleyTurnAngle (t : ℝ) : ℝ :=
  π / 2 * min (max (3 * t - 1) 0) 1

/-- The notch centre follows the corrected circular path during the turn,
joined to horizontal entry and vertical exit translations. -/
noncomputable def hammersleyTranslation (t : ℝ) : ℝ × ℝ :=
  (-(2 / π) * cos (hammersleyTurnAngle t) - (2 / π + 2) * (1 - min (3 * t) 1),
    -(2 / π) * sin (hammersleyTurnAngle t) - 2 * max (3 * t - 2) 0)

/-- The corrected clockwise angle and notch-centre paths are continuous on all of ℝ. -/
theorem hammersleyMotion_continuous :
    Continuous (fun t ↦ -hammersleyTurnAngle t) ∧ Continuous hammersleyTranslation := by
  constructor
  · unfold hammersleyTurnAngle
    continuity
  · unfold hammersleyTranslation hammersleyTurnAngle
    fun_prop

/-- All three phases of the corrected motion remain inside the hallway. -/
theorem hammersleyMotion_containment (t : ℝ) :
    (rigid (-hammersleyTurnAngle t) (hammersleyTranslation t)) ''
      hammersleySofa ⊆ hallway := by
  have radius : 0 < 2 / π := div_pos (by norm_num) pi_pos
  by_cases first : 3 * t ≤ 1
  · have angle : hammersleyTurnAngle t = 0 := by
      norm_num [hammersleyTurnAngle, max_eq_right (by linarith : 3 * t - 1 ≤ 0)]
    have pose : hammersleyTranslation t = (-(2 / π + (2 / π + 2) * (1 - 3 * t)), 0) := by
      simp [hammersleyTranslation, angle, min_eq_left first,
        max_eq_right (by linarith : 3 * t - 2 ≤ 0)]
      ring
    rw [angle, neg_zero, pose]
    have distance : 2 / π ≤ 2 / π + (2 / π + 2) * (1 - 3 * t) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2 / π + 2) (by linarith : 0 ≤ 1 - 3 * t)]
    exact fun _ hp ↦ Or.inl (hammersleySofa_horizontal distance hp)
  · have horizontal : min (3 * t) 1 = 1 := min_eq_right (by linarith)
    by_cases middle : 3 * t ≤ 2
    · have progress : max (3 * t - 1) 0 = 3 * t - 1 := max_eq_left (by linarith)
      have pose : hammersleyTranslation t =
          (-(2 / π) * cos (hammersleyTurnAngle t),
            -(2 / π) * sin (hammersleyTurnAngle t)) := by
        simp [hammersleyTranslation, horizontal,
          max_eq_right (by linarith : 3 * t - 2 ≤ 0)]
      rw [pose]
      apply hammersleySofa_turn
      rw [hammersleyTurnAngle, progress, min_eq_left (by linarith : 3 * t - 1 ≤ 1)]
      constructor <;> nlinarith [pi_pos]
    · have angle : hammersleyTurnAngle t = π / 2 := by
        rw [hammersleyTurnAngle, min_eq_right (le_max_of_le_left (by linarith)), mul_one]
      have pose : hammersleyTranslation t = (0, -(2 / π + 2 * (3 * t - 2))) := by
        simp [hammersleyTranslation, angle, horizontal,
          max_eq_left (by linarith : 0 ≤ 3 * t - 2)]
        ring
      rw [angle, pose]
      exact fun _ hp ↦ Or.inr (hammersleySofa_vertical (by linarith) hp)

/-- The corrected motion starts in the far horizontal arm and ends in the far vertical arm. -/
theorem hammersleyMotion_endpoints :
    (rigid (-hammersleyTurnAngle 0) (hammersleyTranslation 0)) ''
        hammersleySofa ⊆ {p | p.1 ≤ 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} ∧
    (rigid (-hammersleyTurnAngle 1) (hammersleyTranslation 1)) ''
        hammersleySofa ⊆ {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 0} := by
  have radius : 0 < 2 / π := div_pos (by norm_num) pi_pos
  constructor <;> rintro p ⟨q, hq, rfl⟩
  · have bounds := hammersleySofa_subset_box hq
    norm_num [hammersleyTurnAngle, hammersleyTranslation, rigid]
    exact ⟨by linarith [bounds.1.2], bounds.2⟩
  · have bounds := hammersleySofa_subset_box hq
    norm_num [hammersleyTurnAngle, hammersleyTranslation, rigid]
    exact ⟨bounds.2.1, bounds.2.2, by linarith [bounds.1.1]⟩

/-- Hammersley's sofa passes through the hallway using the corrected circular-centre turn. -/
theorem hammersleySofa_movable : Movable hammersleySofa := by
  exact ⟨fun t ↦ -hammersleyTurnAngle t, hammersleyTranslation,
    hammersleyMotion_continuous.1, hammersleyMotion_continuous.2,
    fun t _ ↦ hammersleyMotion_containment t,
    hammersleyMotion_endpoints.1, hammersleyMotion_endpoints.2⟩

end MovingSofaEssay
