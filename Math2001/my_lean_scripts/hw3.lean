import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

-- Problem 4 All three parts below are in [MoP, Section 2.5]:
-- (a) Complete the proof in [MoP, Example 2.5.2].
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : 0 < x * (-t) := by
      calc
        x * (-t) = (-x) * t := by ring
        _ > 0 := by addarith [hxt]
    have hx' : 0 ≤ x := by addarith [hx]
    cancel x at hxt'
    apply ne_of_lt
    have ht : t < 0 := by addarith [hxt']
    apply ht

-- (b) Complete the proof in [MoP, Example 2.5.6].
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

-- (c) Complete the proof in [MoP, Example 2.5.7].
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  calc
    p = (p + p) / 2 := by ring
    _ < (p + q) / 2 := by rel [h]
  calc
    (p + q) / 2 < (q + q) / 2 := by rel [h]
    _ = q := by ring

-- Problem 5 All three parts below are in [MoP, Subsection 2.5.9, Exercises]:
-- (a) Exercise 5. Let be a rational number. Show that there exists a rational number y, such that y^2 > x.
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 2
  nlinarith
  
-- (b) Exercise 6. Let t be a real number, and suppose that there exists a real number a, such that at + 1 < a + t. Show that t != 1,
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  intro ht
  rw [ht] at ha
  simp at ha
  -- apply ne_of_lt ha
  

-- (c) Exercise 7. Let be an integer, and suppose that there exists an integer a such that 2a = m. Show that m != 5
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ham⟩ := h
  intro hm
  rw [hm] at ham
  have H := le_or_gt a 2
  obtain ha | ha := H
  · have ha' := calc
      5 = 2 * a := by rw [ham]
      _ ≤ 2 * 2 := by rel [ha]
      _ = 4 := by ring
    contradiction
  · have ha : a ≥ 3 := by addarith[ha]
    have ha' := calc
      5 = 2 * a := by rw [ham]
      _ ≥ 2 * 3 := by rel [ha]
      _= 6 := by ring
    contradiction     