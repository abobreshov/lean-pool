/-
Copyright (c) 2026 abobreshov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: abobreshov
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Linarith

/-!
# The moving sofa problem

Moser, L. (1966), Problem 66-11, "Moving furniture through a hallway",
SIAM Review 8(3), 381. This citation is grounded by the map's Construct record,
not by Lean. Baek's 2024 optimality theorem is out of scope.

We define the width-one hallway, rigid motions, achievable areas and their supremum.
Movability uses angle and translation paths continuous everywhere on ℝ; containment
is required only for times in [0, 1]. Translating the unit square around the corner
proves that area one is achievable. The lower bound on the supremum is conditional
on an upper bound on all achievable areas. The upper unit half-disc is also movable,
as witnessed by two translations and a clockwise quarter-turn about the corner.
-/

namespace MovingSofaEssay

/-- The two closed width-one arms meeting at the unit square. -/
def hallway : Set (ℝ × ℝ) :=
  {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} ∪
    {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1}

/-- Rotation through θ about the origin followed by translation by v. -/
noncomputable def rigid (θ : ℝ) (v : ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos θ * p.1 - Real.sin θ * p.2 + v.1,
    Real.sin θ * p.1 + Real.cos θ * p.2 + v.2)

/-- A passage through the hallway with paths continuous everywhere on ℝ,
starting in the far horizontal arm and ending in the far vertical arm. -/
def Movable (S : Set (ℝ × ℝ)) : Prop :=
  ∃ (θ : ℝ → ℝ) (v : ℝ → ℝ × ℝ), Continuous θ ∧ Continuous v ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, (rigid (θ t) (v t)) '' S ⊆ hallway) ∧
    (rigid (θ 0) (v 0)) '' S ⊆ {p | p.1 ≤ 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} ∧
    (rigid (θ 1) (v 1)) '' S ⊆ {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 0}

/-- Real areas of bounded measurable sets that can pass through the hallway. -/
noncomputable def achievableAreas : Set ℝ :=
  {a | ∃ S : Set (ℝ × ℝ), MeasurableSet S ∧ Bornology.IsBounded S ∧ Movable S ∧
    (MeasureTheory.volume S).toReal = a}

/-- The supremum of achievable areas is meaningful only given an upper bound on
those areas. This file does not prove one: Hammersley's classical bound 2√2
is not formalized here. -/
noncomputable def sofaConstant : ℝ := sSup achievableAreas

/-- The unit square passes around the corner by horizontal then vertical translation. -/
theorem unitSquare_movable : Movable (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  refine ⟨fun _ ↦ 0, fun t ↦ (min (2 * t) 1 - 1, -(max (2 * t - 1) 0)),
    continuous_const, ?_, ?_, ?_, ?_⟩
  · continuity
  · intro t _ p hp
    obtain ⟨q, ⟨hx, hy⟩, rfl⟩ := hp
    simp only [rigid, Real.cos_zero, Real.sin_zero, one_mul, zero_mul, sub_zero,
      zero_add, hallway, Set.mem_union, Set.mem_setOf_eq]
    by_cases h : 2 * t ≤ 1
    · left
      rw [min_eq_left h, max_eq_right (by linarith : 2 * t - 1 ≤ 0)]
      constructor
      · linarith [hx.2]
      · simpa using hy
    · right
      rw [min_eq_right (by linarith : 1 ≤ 2 * t),
        max_eq_left (by linarith : 0 ≤ 2 * t - 1)]
      exact ⟨by linarith [hx.1], by linarith [hx.2], by linarith [hy.2]⟩
  · rintro p ⟨q, ⟨hx, hy⟩, rfl⟩
    norm_num [rigid] at hx hy ⊢
    exact ⟨by linarith [hx.2], hy⟩
  · rintro p ⟨q, ⟨hx, hy⟩, rfl⟩
    norm_num [rigid] at hx hy ⊢
    exact ⟨hx.1, hx.2, by linarith [hy.2]⟩

/-- The product of two closed unit intervals has Lebesgue area one. -/
theorem volume_unitSquare :
    MeasureTheory.volume (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = 1 := by
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
  norm_num [Real.volume_Icc]

/-- The bounded measurable unit square witnesses that area one is achievable. -/
theorem one_mem_achievableAreas : (1 : ℝ) ∈ achievableAreas := by
  refine ⟨Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
    measurableSet_Icc.prod measurableSet_Icc,
    (Metric.isBounded_Icc 0 1).prod (Metric.isBounded_Icc 0 1), unitSquare_movable, ?_⟩
  rw [volume_unitSquare]
  rfl

/-- The hypothesis is the unproved upper bound on achievable areas; given it,
the unit square shows that the sofa constant is at least one. -/
theorem one_le_sofaConstant_of_bddAbove (h : BddAbove achievableAreas) :
    1 ≤ sofaConstant := by
  exact le_csSup h one_mem_achievableAreas

private theorem halfDisc_rotation_mem {p : ℝ × ℝ}
    (hp : p.1 ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2) {a : ℝ}
    (ha : 0 ≤ a ∧ a ≤ Real.pi / 2) : rigid (-a) (0, 0) p ∈ hallway := by
  have hc : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ha.2⟩
  have hs : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha.1 (by linarith [Real.pi_pos])
  have radius : (Real.cos a * p.1 + Real.sin a * p.2) ^ 2 +
      (-Real.sin a * p.1 + Real.cos a * p.2) ^ 2 ≤ 1 := by
    calc
      _ = (Real.sin a ^ 2 + Real.cos a ^ 2) * (p.1 ^ 2 + p.2 ^ 2) := by ring
      _ ≤ 1 := by rw [Real.sin_sq_add_cos_sq, one_mul]; exact hp.1
  have hx : Real.cos a * p.1 + Real.sin a * p.2 ≤ 1 := by
    nlinarith [sq_nonneg (-Real.sin a * p.1 + Real.cos a * p.2),
      sq_nonneg (Real.cos a * p.1 + Real.sin a * p.2 - 1)]
  have hy : -Real.sin a * p.1 + Real.cos a * p.2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos a * p.1 + Real.sin a * p.2),
      sq_nonneg (-Real.sin a * p.1 + Real.cos a * p.2 - 1)]
  simp only [neg_mul] at hy
  simp only [rigid, Real.cos_neg, Real.sin_neg, neg_mul, sub_neg_eq_add, add_zero,
    hallway, Set.mem_union, Set.mem_setOf_eq]
  by_cases h : 0 ≤ p.1
  · exact Or.inr ⟨add_nonneg (mul_nonneg hc h) (mul_nonneg hs hp.2), hx, hy⟩
  · exact Or.inl ⟨hx, add_nonneg
      (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hs (le_of_not_ge h)))
      (mul_nonneg hc hp.2), hy⟩

/-- The closed upper unit half-disc passes through by translation into the corner,
a clockwise quarter-turn about the corner, then downward translation. -/
theorem halfDisc_movable : Movable {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} := by
  refine ⟨fun t ↦ -(Real.pi / 2 * min (max (3 * t - 1) 0) 1),
    fun t ↦ (min (3 * t) 1 - 1, -(max (3 * t - 2) 0)), ?_, ?_, ?_, ?_, ?_⟩
  · continuity
  · continuity
  · intro t _ p hp
    obtain ⟨q, hq, rfl⟩ := hp
    dsimp only
    have hx : q.1 ≤ 1 := by nlinarith [hq.1, sq_nonneg q.2, sq_nonneg (q.1 - 1)]
    have hy : q.2 ≤ 1 := by nlinarith [hq.1, sq_nonneg q.1, sq_nonneg (q.2 - 1)]
    by_cases first : 3 * t ≤ 1
    · have zero : max (3 * t - 1) 0 = 0 := max_eq_right (by linarith)
      have stationary : max (3 * t - 2) 0 = 0 := max_eq_right (by linarith)
      simp only [zero, stationary, min_eq_left first]
      norm_num [rigid, hallway]
      exact Or.inl ⟨by linarith, hq.2, hy⟩
    · have horizontal : min (3 * t) 1 = 1 := min_eq_right (by linarith)
      by_cases middle : 3 * t ≤ 2
      · have stationary : max (3 * t - 2) 0 = 0 := max_eq_right (by linarith)
        have progress : max (3 * t - 1) 0 = 3 * t - 1 := max_eq_left (by linarith)
        rw [horizontal, stationary, progress, min_eq_left (by linarith : 3 * t - 1 ≤ 1)]
        norm_num only [sub_self, neg_zero]
        apply halfDisc_rotation_mem hq
        constructor <;> nlinarith [Real.pi_pos]
      · have progress : min (max (3 * t - 1) 0) 1 = 1 :=
          min_eq_right (le_max_of_le_left (by linarith))
        rw [horizontal, progress, max_eq_left (by linarith : 0 ≤ 3 * t - 2)]
        norm_num [rigid, hallway, Real.cos_pi_div_two, Real.sin_pi_div_two]
        refine Or.inr ⟨hq.2, hy, ?_⟩
        nlinarith [hq.1, sq_nonneg q.2, sq_nonneg (q.1 + 1)]
  · rintro p ⟨q, hq, rfl⟩
    norm_num [rigid]
    exact ⟨by nlinarith [hq.1, sq_nonneg q.2, sq_nonneg (q.1 - 1)], hq.2,
      by nlinarith [hq.1, sq_nonneg q.1, sq_nonneg (q.2 - 1)]⟩
  · rintro p ⟨q, hq, rfl⟩
    norm_num [rigid, Real.cos_pi_div_two, Real.sin_pi_div_two]
    exact ⟨hq.2, by nlinarith [hq.1, sq_nonneg q.1, sq_nonneg (q.2 - 1)],
      by nlinarith [hq.1, sq_nonneg q.2, sq_nonneg (q.1 + 1)]⟩

end MovingSofaEssay
