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

-- Problem 4 There are four parts, all in [MoP, Section 5.1]:
-- (a) Exercise 11 in [MoP, Subsection 5.1.7, Exercises].
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro h_Px
    obtain ⟨x, h_P⟩ := h_Px
    have h_eq := h x
    obtain ⟨h_PQ, h_QP⟩ := h_eq
    use x
    apply h_PQ h_P
  · intro h_Qx
    obtain ⟨x, h_Q⟩ := h_Qx
    have h_eq := h x
    obtain ⟨h_PQ, h_QP⟩ := h_eq
    use x
    apply h_QP h_Q
     

-- (b) Exercise 12 in [MoP, Subsection 5.1.7, Exercises].
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro h_Pxy
    obtain ⟨x, h_Pxy⟩ := h_Pxy
    obtain ⟨y, h_Pxy⟩ := h_Pxy
    use y
    use x
    apply h_Pxy
  · intro h_Pxy
    obtain ⟨y, h_Pxy⟩ := h_Pxy
    obtain ⟨x, h_Pxy⟩ := h_Pxy
    use x
    use y
    apply h_Pxy

-- (c) Exercise 13 in [MoP, Subsection 5.1.7, Exercises].
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro h_Pxy
    intro y
    intro x
    apply h_Pxy x y
  · intro h_Pxy
    intro x
    intro y
    apply h_Pxy y x


-- (d) Exercise 14 in [MoP, Subsection 5.1.7, Exercises].
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro h_Px_and_Q
    obtain ⟨h_Px, h_Q⟩ := h_Px_and_Q
    obtain ⟨x, h_Px⟩ := h_Px
    use x
    apply And.intro h_Px h_Q
  · intro h_Px_and_Q
    obtain ⟨x, h_Px_and_Q⟩ := h_Px_and_Q
    obtain ⟨h_Px, h_Q⟩ := h_Px_and_Q
    constructor
    · use x
      apply h_Px
    · apply h_Q

-- Problem 5 There are three parts, all in [MoP, Section 5.2]:
-- (a) Exercise 1 in [MoP, Subsection 5.2.7, Exercises].
def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

lemma tribalanced_zero : Tribalanced 0 := by
  dsimp [Tribalanced]
  intros n
  simp
  numbers

lemma not_tribalanced_two : ¬ Tribalanced 2 := by
  dsimp [Tribalanced]
  simp
  use 2
  simp
  numbers

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h_1 : Tribalanced 1
  · use 1
    constructor
    · apply h_1
    · numbers
      have h_not2 := not_tribalanced_two
      apply h_not2
  · use 0
    constructor
    · have h_0 := tribalanced_zero
      apply h_0
    · numbers
      apply h_1

-- (b) Exercise 3 in [MoP, Subsection 5.2.7, Exercises].
def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

theorem not_superpowered_zero : ¬ Superpowered 0 := by
  intro h
  have one_prime : Prime (0 ^ 0 ^ 0 + 1) := h 0
  conv at one_prime => numbers
  have : ¬ Prime 1 := not_prime_one
  contradiction 

theorem superpowered_one : Superpowered 1 := by
 intro n
 conv => ring_nf -- Try this: ring_nf
 apply prime_two

theorem not_superpowered_two : ¬ Superpowered 2 := by
  intro h
  have _4294967297_prime := h 5
  conv at _4294967297_prime => numbers
  have not_4294967297_prime : ¬  Prime 4294967297 := by
    apply not_prime 641 6700417
    numbers
    numbers
    numbers
  contradiction

example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  numbers
  constructor
  . apply superpowered_one
  . apply not_superpowered_two