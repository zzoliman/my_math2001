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

-- Problem 4 There are four parts, all in [MoP, Section 5.3]:
-- (a) Complete the proof in [MoP, Example 5.3.5].
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n ^ 2 ≥ 2 ^ 2 := by rel [hn]
      _ > 2 := by numbers

-- (b) Exercise 2 in [MoP, Subsection 5.3.6, Exercises].
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro h_left
    by_cases h_right : P ∧ ¬ Q
    · apply h_right
    · have contra_1 : P → Q
      · intro h_p
        by_cases h_q : Q
        · apply h_q
        · have contra_2 : P ∧ ¬ Q := And.intro h_p h_q
          contradiction
      contradiction
  · intro h_right
    obtain ⟨h1, h2⟩ := h_right
    intro h_pq
    have h_q := by apply h_pq h1
    contradiction

-- Problem 5 There are three parts, all in [MoP, Section 5.3]:
-- (a) Exercise 9 in [MoP, Subsection 5.3.6, Exercises].
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  intro h_p
  use k
  constructor
  . apply hk
  . apply And.intro hk1 hkp

-- (b) Exercise 10 in [MoP, Subsection 5.3.6, Exercises]
example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    have h_prime := prime_test hp2 H
    contradiction
  push_neg at H
  apply H
