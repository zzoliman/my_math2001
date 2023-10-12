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

-- Problem 4 There are two parts, both in [MoP, Section 4.2]:
-- (a) Exercise 2 in [MoP, Subsection 4.2.10, Exercises].
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h_left
    obtain ⟨a, h_a⟩ := h_left
    constructor
    · use 9 * a
      calc
        n = 63 * a := by rw [h_a]
        _ = 7 * (9 * a) := by ring
    · use 7 * a
      calc
        n = 63 * a := by rw [h_a]
        _ = 9 * (7 * a) := by ring
  · intro h_right
    obtain ⟨h_7, h_9⟩ := h_right
    obtain ⟨a, h_a⟩ := h_7
    obtain ⟨b, h_b⟩ := h_9
    use (4 * b - 3 * a)
    calc
      n = 28 * n - 27 * n := by ring
      _ = 28 * (9 * b) - 27 * n := by rw [h_b]
      _ = 28 * (9 * b) - 27 * (7 * a) := by rw [h_a]
      _ = 63 * (4 * b - 3 * a) := by ring

-- (b) Exercise 5 in [MoP, Subsection 4.2.10, Exercises].
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intros h_left
    have h_k2_lt_9 : k ^ 2 < 3 ^ 2 := by
      calc
        k ^ 2 ≤ 6 := by rel [h_left]
        _ < 3 ^ 2 := by numbers
    cancel 2 at h_k2_lt_9
    have h_gte_0 : k ≥ 0 := by extra
    interval_cases k
    all_goals simp
  · intro h_left
    cases h_left with
    | inl h_0 =>
      calc
            k ^ 2 = 0 ^ 2 := by rw [h_0]
            _ ≤ 6 := by numbers
    | inr h_12 =>
      cases h_12 with
        | inl h_1 =>
          calc
            k ^ 2 = 1 ^ 2 := by rw [h_1]
            _ ≤ 6 := by numbers
        | inr h_2 =>
          calc
            k ^ 2 = 2 ^ 2 := by rw [h_2]
            _ ≤ 6 := by numbers

-- Problem 5 There are three parts, all in [MoP, Section 4.3]:
-- (a) Complete the proof in [MoP, Example 4.3.2].
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intro a h_gte_1 h_lte_3
    have h_1 : -1 ≤ a - 2 := by addarith [h_gte_1]
    have h_2 : a - 2 ≤ 1 := by addarith [h_lte_3]
    have h : (a - 2) ^ 2 ≤ 1 ^ 2 := by apply sq_le_sq' h_1 h_2
    numbers at h
    apply h
  · intro y hy
    have h_1 := hy 1
    have h_3 := hy 3
    have h_1' := by
      apply h_1
      simp
      simp
    have h_3' := by
      apply h_3
      simp
      simp
    have h_lte_0 : (y - 2) ^ 2 ≤ 0 := by
      calc
        (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring
        _ ≤ (1 + (3 - y) ^ 2 - 2) / 2 := by rel [h_1']
        _ ≤ (1 + 1 - 2) / 2 := by rel [h_3']
        _ = 0:= by numbers
    have h_gte_0 : (y - 2) ^ 2 ≥ 0 := by extra
    have h_eq_0 : (y - 2) ^ 2 = 0 := by apply le_antisymm h_lte_0 h_gte_0
    simp at h_eq_0
    calc
      y = 2 := by addarith [h_eq_0]

-- (b) Exercise 1 in [MoP, Subsection 4.3.5, Exercises].
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · numbers
  · intro y h_y
    have h_y' : 4 * y = 4 * 3 := by addarith [h_y]
    cancel 4 at h_y'

-- (c) Exercise 2 in [MoP, Subsection 4.3.5, Exercises].
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  · simp
  · intro y h_y
    have h_gte_0 : y ≥ 0 := by extra
    have h_lte_0 := by apply h_y 0
    apply le_antisymm h_lte_0 h_gte_0

-- Problem 6 There are three parts, all in [MoP, Section 4.4]:
-- (a) Complete the proof in [MoP, Example 4.4.4].
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  · -- the case `1 < m`
    right
    have h_m_lt_p : m ≤ p := by apply Nat.le_of_dvd hp' hmp
    obtain h1 | h2 : m = p ∨ m < p := eq_or_lt_of_le h_m_lt_p
    apply h1
    have h_contra := by apply H m hm_left h2 hmp
    contradiction

-- (b) Complete the proof in [MoP, Example 4.4.5].
example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  sorry

-- (c) Exercise 1 in [MoP, Subsection 4.4.6, Exercises].
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  cancel n at h

-- (d) Exercise 5 in [MoP, Subsection 4.4.6, Exercises].
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨h_p, h⟩ := h
  obtain h_gt | h_eq := lt_or_eq_of_le h_p
  . right
    have h_odd: ¬ Nat.Even p:= by
      intro h_even
      obtain ⟨x, h_x⟩ := h_even
      have h_div_2: 2 ∣ p := by
        use x
        rw [h_x]
      obtain h_2 := h 2 h_div_2
      obtain h_l| h_r := h_2
      . contradiction
      . rw [h_r] at h_gt
        have h_gt' : 0 < 0 := by addarith[h_gt]
        contradiction
    obtain h_even' | h_odd' := Nat.even_or_odd p
    . contradiction
    . apply h_odd'
  . left
    rw[h_eq]