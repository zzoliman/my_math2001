--7|n and 9|n -> 63|n

--a|n and b|n -> a*b|n
-- 6|n and 14|n -> 84|n

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

/- Bezout -/
example {n : ℤ} : 7 ∣ n ∧ 11 ∣ n → 77 ∣ n := by
  intros h
  obtain ⟨h7, h11⟩ := h
  dsimp [(.∣.)] at *
  obtain ⟨a,ha⟩ := h7
  obtain ⟨b,hb⟩ := h11
  use 2 * a - 3 * b
  calc
    n = 22 * n - 21 * n := by ring
    _ = 22 * (7 * a) - 21 * n := by rw[ha]
    _ = 22 * (7 * a) - 21 * (11 * b) := by rw[hb]
    _ = 77 * (2 * a - 3 * b) := by ring

/- Showing ∃! -/
  example : ∃! a : ℝ , 3 * a + 1 = 7 := by 
    use 2
    simp
    constructor
    · numbers
    · intros y h
      have h' : 3 * y = 3 * 2 :=
      calc
        3 * y = 3 * y + 1 - 1 := by ring
        _ = 7 - 1 := by rw [h]
        _ = 3 * 2 := by numbers
      cancel 3 at h'

/- Using ∃! -/
example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring

  example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
    use 4
    dsimp
    constructor
    · constructor
      · numbers
      constructor
      · numbers
      use 2
      numbers
    intro r hr
    obtain ⟨hr1, hr2, q, hr3⟩ := hr
    have :=
      calc
        5 * 1 < 14 - r := by addarith [hr2]
        _ = 5 * q := by rw [hr3]
    cancel 5 at this
    have :=
      calc
        5 * q = 14 - r := by rw [hr3]
        _ < 5 * 3 := by addarith [hr1]
    cancel 5 at this
    interval_cases q
    addarith [hr3]