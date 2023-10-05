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

-- Problem 4 All four parts below are in [MoP, Section 3.1]. The first three parts should be relatively easy, as warm-up for the fourth part.

-- (a) Complete the proof in [MoP, Example 3.1.4].
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring

-- (b) Complete the proof in [MoP, Example 3.1.6].
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨k_1, hk_1⟩ := hx
  obtain ⟨k_2, hk_2⟩ := hy
  use 2 * k_1 * k_2 + 3 * k_2 + k_1 + 1
  calc
    x * y + 2 * y = (2 * k_1 + 1) * (2 * k_2 + 1) + 2 * (2 * k_2 + 1) := by rw [hk_1, hk_2]
    _ = 2 * (2 * k_1 * k_2 + 3 * k_2 + k_1 + 1) + 1 := by ring

-- (c) Complete the proof in [MoP, Example 3.1.8].
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even] at *
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 2 * k ^ 2 + 2 * k - 3
  calc
    n ^ 2 + 2 * n - 5 = (k + k) ^ 2 + 2 * (k + k) - 5 := by rw [hk]
    _ = 2 * (2 * k ^ 2 + 2 * k - 3) + 1 := by ring

-- (d) Exercise 14 (the last one) in [MoP, Subsection 3.1.10, Exercises].
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha | ha := Int.even_or_odd a
  · obtain hb | hb := Int.even_or_odd b
    · left
      obtain ⟨k, hk⟩ := ha
      obtain ⟨k2, hk2⟩ := hb
      use k - k2
      calc
        a - b = 2 * k - b := by rw [hk]
        _ = 2 * k - 2 * k2 := by rw [hk2]
        _ = (k - k2) + (k - k2) := by ring
    · obtain hc | hc := Int.even_or_odd c
      · right
        left
        obtain ⟨k, hk⟩ := ha
        obtain ⟨k2, hk2⟩ := hc
        use k + k2
        calc
          a + c = 2 * k + c := by rw [hk]
          _ = 2 * k + 2 * k2 := by rw [hk2]
          _ = (k + k2) + (k + k2) := by ring
      · right
        right
        obtain ⟨k, hk⟩ := hb
        obtain ⟨k2, hk2⟩ := hc
        use k - k2
        calc
          b - c = 2 * k + 1 - c := by rw [hk]
          _ = 2 * k + 1 - (2 * k2 + 1) := by rw [hk2]
          _ = (k - k2) + (k - k2) := by ring
  · obtain hb | hb := Int.even_or_odd b
    · obtain hc | hc := Int.even_or_odd c
      · right
        right
        obtain ⟨k, hk⟩ := hb
        obtain ⟨k2, hk2⟩ := hc
        use k - k2
        calc
          b - c = 2 * k - c := by rw [hk]
          _ = 2 * k - (2 * k2) := by rw [hk2]
          _ = (k - k2) + (k - k2) := by ring
      · right
        left
        obtain ⟨k, hk⟩ := ha
        obtain ⟨k2, hk2⟩ := hc
        use k + k2 + 1
        calc
          a + c = 2 * k + 1 + c := by rw [hk]
          _ = 2 * k + 1 + (2 * k2 + 1) := by rw [hk2]
          _ = (k + k2 + 1) + (k + k2 + 1) := by ring

    · left
      obtain ⟨k, hk⟩ := ha
      obtain ⟨k2, hk2⟩ := hb
      use k - k2
      calc
        a - b = 2 * k + 1 - b := by rw [hk]
        _ = 2 * k + 1 - (2 * k2 + 1) := by rw [hk2]
        _ = (k - k2) + (k - k2) := by ring

-- Problem 5 All four parts below are in [MoP, Section 4.1]. The first three parts should be relatively easy, as warm-up for the fourth part.

-- (a) Complete the proof in [MoP, Example 4.1.3].
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h1 : (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain h_a | h_b := h1
  · calc
      b = 2 * ((a + b) / 2) - a := by ring
      _ ≥ 2 * a - a := by rel [h_a]
      _ = a := by ring
  · calc
      a = 2 * ((a + b) / 2) - b := by ring
      _ ≤ 2 * b - b := by rel [h_b]
      _ = b := by ring

-- (b) Complete the proof in [MoP, Example 4.1.6].
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x
  intro y
  intro h_xy
  have h_x3 : (x + y) ^ 2 ≤ 3 ^ 2 := by
    calc
      (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
      _ = 2 * (x ^ 2 + y ^ 2) := by ring
      _ ≤ 2 * 4 := by rel [h_xy]
      _ ≤ 3 ^ 2 := by numbers
  have h_3 : (0 ≤ 3) := by numbers
  have h_ : -3 ≤ x + y ∧ x + y ≤ 3 := by 
    apply abs_le_of_sq_le_sq' h_x3
    numbers
  obtain ⟨h_ge, _⟩ := h_ 
  apply h_ge
  
-- (c) Exercise 2 in [MoP, Subsection 4.1.10, Exercises].
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h_3 := hn 3
  simp at h_3
  have h_5 := hn 5
  simp at h_5
  obtain ⟨b, hb⟩ := h_3
  obtain ⟨a, ha⟩ := h_5
  use 2 * a - b
  calc
    n = 6 * n - 5 * n := by ring
    _ = 6 * (5 * a) - 5 * n := by rw [ha]
    _ = 6 * (5 * a) - 5 * (3 * b) := by rw [hb]
    _ = 15 * (2 * a - b) := by ring

-- (d) Exercise 4 in [MoP, Subsection 4.1.10, Exercises].
example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  dsimp
  use 20
  intro x
  intro h_x20
  calc
    x ^ 3 + 3 * x = x * x ^ 2 + 3 * x := by ring
    _ ≥ 20 * x ^ 2 + 3 * x := by rel [h_x20] 
    _ ≥ 20 * x ^ 2 + 3 * (20) := by rel [h_x20]
    _ = 7 * x ^ 2 + 13 * x * x + 60 := by ring
    _ ≥ 7 * x ^ 2 + (13 * 20 * 20) + 60 := by rel [h_x20]
    _ = 7 * x ^ 2 + 5248 + 12 := by ring
    _ ≥ 7 * x ^ 2 + 12 := by extra

-- Problem 6 There are two parts, both in [MoP, Section 4.2], with (a) a little easier than (b):

-- (a) Complete the proof in [MoP, Example 4.2.5].
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have h_fac : (x + 3) * (x - 2) = 0 := by
      calc
        (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
        _ = 0 := by rw [h]
    have h_sols := eq_zero_or_eq_zero_of_mul_eq_zero h_fac
    cases h_sols with
    | inl l => 
      left
      have h3 : x = -3 := by 
        calc
          x = x + 3 - 3 := by ring
          _ = 0 - 3 := by rw [l]
          _ = -3 := by numbers
      apply h3
    | inr r =>
      right
      have hn2 : x = 2 := by
        calc
          x = x - 2 + 2 := by ring
          _ = 0 + 2 := by rw [r]
          _ = 2 := by numbers
      apply hn2
  · intro h_sols
    cases h_sols with
    | inl l =>
      calc
        x ^ 2 + x - 6 = (-3) ^ 2 + (-3) - 6 := by rw [l]
        _ = 0 := by numbers
    | inr r =>
      calc
        x ^ 2 + x - 6 = (2) ^ 2 + (2) - 6 := by rw [r]
        _ = 0 := by numbers

-- (b) Complete the proof in [MoP, Example 4.2.6].
example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h_ineq
    have h_sq : (2 * a - 5) ^ 2 ≤ 1 ^ 2 := by
      calc
        (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
        _ ≤ 4 * (-1) + 5 := by rel [h_ineq]
        _ = 1 ^ 2 := by numbers
    have h_abs_sq : (-1 ≤ 2 * a - 5) ∧ (2 * a - 5 ≤ 1) := by
      apply abs_le_of_sq_le_sq' h_sq
      numbers
    obtain ⟨h_n1, h_1⟩ := h_abs_sq
    have h_2 : 2 * 2 ≤ 2 * a := by addarith [h_n1]
    cancel 2 at h_2
    have h_3 : 2 * 3 ≥ 2 * a := by addarith [h_1]
    cancel 2 at h_3
    have h_cases := le_or_succ_le a 2
    cases h_cases with
    | inl l =>
      left
      have a2 : a = 2 := by 
        apply le_antisymm l h_2
      apply a2
    | inr r =>
      right
      have a3 : a = 3 := by 
        apply le_antisymm h_3 r
      apply a3
  · intro h_sols 
    cases h_sols with
    | inl l =>
      extra
    | inr r =>
      extra