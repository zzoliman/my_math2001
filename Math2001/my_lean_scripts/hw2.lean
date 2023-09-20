import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

-- Problem 6
-- Excercise 1
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 := by
  have h3 :=
  calc
    x + 3 ≥ 2 * y := by rel [h1]
    _ ≥ 2 * 1 := by rel [h2]
    _ = 2 := by numbers
  addarith [h3]

-- Excercise 2
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 := by
  calc
    a + b = ((a) + (a + 2 * b)) / 2 := by ring
    _ ≥ (3 + 4) / 2 := by rel [h1, h2]
    _ = 7/2 := by ring
    _ ≥ 3 := by numbers

-- Excercise 3
example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = x * x ^ 2 - 8 * x ^ 2 + 2 * x := by ring
    _ ≥ 9 * x ^ 2 - 8 * x ^ 2 + 2 * x := by rel [hx]
    _ = x ^ 2 + 2 * x := by ring
    _ = x * x + 2 * x := by ring
    _ ≥ 9 * x + 2 * x := by rel [hx]
    _ = 11 * x := by ring
    _ ≥ 11 * 9 := by rel [hx]
    _ ≥ 3 := by numbers