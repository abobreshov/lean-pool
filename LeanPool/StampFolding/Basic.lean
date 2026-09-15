/-
Copyright (c) 2026 abobreshov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: abobreshov
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Filter

/-!
# Stamp Folding

Source: url:https://oeis.org/A000136
Authors: abobreshov
Status: verified
Main declarations: `StampFolding.card_foldings_five`
Tags: combinatorics, stamp-folding, finite-enumeration
MSC: 05A15
-/

/-!
## Declared permutation model

A permutation maps each stamp label in `Fin n` to its position in the pile.
Hinge `i` joins stamps `i` and `i + 1` when `i + 1 < n`, and lies on side `i % 2`.
Two hinges cross when their position intervals strictly interleave. A folding
has no crossing pair on the same side. Counts distinguish every labelled pile
order; there is no quotient by reversal or reflection.

The counts for sizes one through five are proved by decidable finite enumeration.
This project does not prove that the permutation model is the physical folding
problem, any count for n ≥ 6, or anything about A001011.
-/

namespace StampFolding

/-- Two intervals with unordered endpoints cross when their endpoints strictly interleave. -/
def Interleave (a b c d : ℕ) : Prop :=
  (min a b < min c d ∧ min c d < max a b ∧ max a b < max c d) ∨
    (min c d < min a b ∧ min a b < max c d ∧ max c d < max a b)

instance (a b c d : ℕ) : Decidable (Interleave a b c d) := by
  unfold Interleave
  infer_instance

/-- A pile-position permutation is a folding when no same-parity hinges cross.
The successor bounds exclude a hinge from the last stamp back to the first. -/
def IsFolding {n : ℕ} (position : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, ∀ hi : i.val + 1 < n, ∀ hj : j.val + 1 < n,
    i.val % 2 = j.val % 2 →
      ¬ Interleave (position i).val (position ⟨i.val + 1, hi⟩).val
        (position j).val (position ⟨j.val + 1, hj⟩).val

instance {n : ℕ} (position : Equiv.Perm (Fin n)) : Decidable (IsFolding position) := by
  unfold IsFolding
  infer_instance

/-- All pile-position permutations satisfying the declared no-crossing condition. -/
def foldings (n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter IsFolding

/-- The declared model has one folding of one stamp. -/
theorem card_foldings_one : (foldings 1).card = 1 := by
  decide +kernel

/-- The declared model has two foldings of two stamps. -/
theorem card_foldings_two : (foldings 2).card = 2 := by
  decide +kernel

/-- The declared model has six foldings of three stamps. -/
theorem card_foldings_three : (foldings 3).card = 6 := by
  decide +kernel

/-- The declared model has sixteen foldings of four stamps. -/
theorem card_foldings_four : (foldings 4).card = 16 := by
  decide +kernel

/-- The declared model has fifty foldings of five stamps. -/
theorem card_foldings_five : (foldings 5).card = 50 := by
  decide +kernel

end StampFolding
