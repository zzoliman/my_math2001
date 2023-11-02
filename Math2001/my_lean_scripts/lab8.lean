import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.Numbers
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
set_option push_neg.use_distrib true

example (P : Prop) : ¬ (¬ P) ↔ P := by
  sorry

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  sorry

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by 
  sorry

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) := by 
  sorry

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by 
  sorry

example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  sorry 