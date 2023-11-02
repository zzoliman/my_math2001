/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/-! # Section 2.2 -/

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt 
  extra 

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := h1
  extra

/-! # Exercises -/

example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt 
  have hm' : m = 4 := by addarith [hm] 
  calc 
    3 * m = 3 * 4 := by rw [hm'] 
    _ > 6 := by numbers 

/-! # Section 2.5 -/

example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers

example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra

example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers 

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/

example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3 
  numbers 

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 9, 2
  numbers 

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -(1/2) 
  constructor 
  numbers 
  numbers 

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3 
  numbers 

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b)
    (ha' : 0 ≤ a) (hb' : 0 ≤ b) (hc' : 0 ≤ c) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (1/2) * (-a + b + c), (1/2) * (a - b + c), (1/2) * (a + b - c)
  have ha'' : 0 ≤ (1/2) * (-a + b + c) := 
  calc 
    0 = (1/2) * (a - a) := by ring 
    _ ≤ (1/2) * (b + c - a) := by rel [ha] 
    _ = (1/2) * (-a + b + c) := by ring 
  have hb'' : 0 ≤ (1/2) * (a - b + c) := 
  calc 
    0 = (1/2) * (b - b) := by ring 
    _ ≤ (1/2) * (a + c - b) := by rel [hb] 
    _ = (1/2) * (a - b + c) := by ring 
  have hc'' : 0 ≤ (1/2) * (a + b - c) := 
  calc 
    0 = (1/2) * (c - c) := by ring 
    _ ≤ (1/2) * (a + b - c) := by rel [hc] 
  constructor 
  apply ha'' 
  constructor 
  apply hb'' 
  constructor 
  apply hc'' 
  constructor 
  ring
  constructor 
  ring 
  ring 
