import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

/- 5.1 Exercises -/

example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by sorry 

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by sorry 

example (P : Prop) : ¬(P ∧ ¬ P) := by sorry 

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by sorry 

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by sorry 

example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by sorry 

example (P : Prop) : (P ∧ P) ↔ P := by sorry 

example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by sorry 

example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by sorry 

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by sorry 

/- 5.2 Reading -/

def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

#numbers 0 ^ 0 ^ 0 + 1 -- 1
#numbers 0 ^ 0 ^ 1 + 1 -- 2
#numbers 0 ^ 0 ^ 2 + 1 -- 2

theorem not_superpowered_zero : ¬ Superpowered 0 := by
  intro h
  have one_prime : Prime (0 ^ 0 ^ 0 + 1) := h 0
  conv at one_prime => numbers -- simplifies that statement to `Prime 1`
  have : ¬ Prime 1 := not_prime_one
  contradiction

#numbers 1 ^ 1 ^ 0 + 1 -- 2
#numbers 1 ^ 1 ^ 1 + 1 -- 2
#numbers 1 ^ 1 ^ 2 + 1 -- 2

theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two

#numbers 2 ^ 2 ^ 0 + 1 -- 3
#numbers 2 ^ 2 ^ 1 + 1 -- 5
#numbers 2 ^ 2 ^ 2 + 1 -- 17
#numbers 2 ^ 2 ^ 3 + 1 -- 257
#numbers 2 ^ 2 ^ 4 + 1 -- 65537

#numbers 3 ^ 3 ^ 0 + 1 -- 4
#numbers 3 ^ 3 ^ 1 + 1 -- 28
#numbers 3 ^ 3 ^ 2 + 1 -- 19684

theorem not_superpowered_three : ¬ Superpowered 3 := by
  intro h
  dsimp [Superpowered] at h
  have four_prime : Prime (3 ^ 3 ^ 0 + 1) := h 0
  conv at four_prime => numbers -- simplifies that statement to `Prime 4`
  have four_not_prime : ¬ Prime 4
  · apply not_prime 2 2
    · numbers -- show `2 ≠ 1` 
    · numbers -- show `2 ≠ 4` 
    · numbers -- show `4 = 2 * 2`
  contradiction

example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  by_cases h2 : Superpowered 2
  · use 2
    constructor
    · apply h2
    · apply not_superpowered_three
  · use 1
    constructor
    · apply superpowered_one
    · apply h2      

example {P : Prop} (hP : ¬¬P) : P := by
  by_cases hP : P
  · apply hP
  · contradiction

/- 5.2 Exercises -/

example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by sorry