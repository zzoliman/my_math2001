/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Tactic.Addarith

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/-! # Section 1.5: A shortcut -/
/-
For the purposes of this book, let’s draw the line as follows: if a fact can be deduced from
another fact simply by adding/subtracting terms from both sides (no multiplication/division/etc),
then there is no need to write out a full proof by calculation.

For use in Lean, I’ve provided a tactic `addarith` which carries out simple deductions like this.
-/

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by addarith [h1]

example {a b : ℤ} (ha : a - 2 * b = 1) : a = 2 * b + 1 := by addarith [ha]

example {x y : ℚ} (hx : x = 2) (hy : y ^ 2 = -7) : x + y ^ 2 = -5 :=
  calc
    x + y ^ 2 = x - 7 := by addarith [hy]
    _ = -5 := by addarith [hx]    

-- It is also fine to do this for inequalities, if all that’s involved in the inequality deduction is adding/subtracting terms. For example,
example {s t : ℝ} (h : t = 4 - s * t) : t + s * t > 0 := by addarith [h]

example {m n : ℝ} (h1 : m ≤ 8 - n) : 10 > m + n := by addarith [h1]


-- Check that `addarith` can't verify this deduction!
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := sorry
