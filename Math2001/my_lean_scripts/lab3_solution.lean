/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/-! # Section 1.4: Proving inequalities -/

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p

lemma de_morgan_1 {p q : Prop} : ¬(p ∨ q) → (¬p ∧ ¬q) := by 
  intros h 
  have h_notp : ¬p := by
    intros h_p 
    apply h (Or.inl h_p) 
  have h_notq : ¬q := by 
    intros h_q 
    apply h (Or.inr h_q)
  apply And.intro h_notp h_notq 

lemma de_morgan_4 {p q : Prop} : ¬(p ∧ q) → (¬p ∨ ¬q) := by 
  intros h 
  have dubneg : ¬¬(¬p ∨ ¬q) := by 
    intros not_notp_or_notq 
    have notnotp : ¬¬p := by 
      intros notp 
      have contra : ¬p ∨ ¬q := Or.inl notp 
      contradiction
    have pee : p := notnotE notnotp                   --uses DNE
    have notnotq : ¬¬q := by 
      intros notq 
      have contra : ¬p ∨ ¬q := Or.inr notq 
      contradiction 
    have que : q := notnotE notnotq                   --uses DNE
    have p_and_q : p ∧ q := And.intro pee que 
    contradiction 
  apply notnotE dubneg                                --uses DNE

-- Example 1.4.1
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by numbers

-- Example 1.4.2
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by ring 
    _ ≤ (3 + (s + 3) - s) / 2 := by rel [h2,h1] 
    _ = 3 := by ring 

-- Example 1.4.3
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  calc 
    x + y ≤ x + (x + 5) := by rel [h1] 
    _ = 2 * x + 5 := by ring 
    _ ≤ 2 * (-2) + 5 := by rel [h2] 
    _ = 1 := by ring 
    _ < 2 := by numbers 

-- Example 1.4.4
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by rel [h5, h4] 
    _ ≤ A * B + A * B + A * v := by rel [h8, h9, h8] 
    _ ≤ A * B + A * B + 1 * v := by rel [h2] 
    _ ≤ A * B + A * B + B * v := by rel [h3] 
    _ < A * B + A * B + B * A := by rel [h9] 
    _ = 3 * A * B := by ring 

-- Example 1.4.5
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by ring 
    _ ≥ 10 * t - 3 * t - 17 := by rel [ht] 
    _ = 7 * t - 17 := by ring
    _ ≥ 7 * 10 - 17 := by rel [ht] 
    _ ≥ 5 := by numbers 

-- Example 1.4.6
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc 
    n ^ 2 = n * n := by ring 
    _ ≥ 5 * n := by rel [hn] 
    _ = 2 * n + 3 * n := by ring 
    _ ≥ 2 * n + 3 * 5 := by rel [hn] 
    _ = 2 * n + 11 + 4 := by ring 
    _ > 2 * n + 11 := by extra 

-- Example 1.4.7
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 :=
  calc
    n ≤ m ^ 2 + n := by extra
    _ ≤ 2 := by rel [h]


-- Example 1.4.8
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra 
    _ = 2 * (x ^ 2 + y ^ 2) := by ring 
    _ ≤ 2 * 1 := by rel [h] 
    _ < 3 := by numbers 

-- Example 1.4.9
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by extra 
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring 
    _ ≤ 2 * (8 * b) + 8 * a + a := by rel [h3] 
    _ = 7 * b + 9 * (a + b) := by ring 
    _ ≤ 7 * b + 9 * 8 := by rel [h3] 
    _ = 7 * b + 72 := by ring 

-- Example 1.4.10
example {a b c : ℝ} :
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 :=
  calc
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)
      ≤ 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2
          + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2
          + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) := by extra
    _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by ring


/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/

--First three exercises omitted because they're on the homework.

example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  calc 
    n ^ 4 - 2 * n ^ 2 = n * n ^ 3 - 2 * n ^ 2 := by ring 
    _ ≥ 10 * n ^ 3 - 2 * n ^ 2 := by rel [hn] 
    _ = 3 * n ^ 3 + 7 * n ^ 3 - 2 * n ^ 2 := by ring 
    _ = 3 * n ^ 3 + n ^ 2 * (7 * n - 2) := by ring 
    _ ≥ 3 * n ^ 3 + n ^ 2 * (7 * 10 - 2) := by rel [hn] 
    _ > 3 * n ^ 3 := by extra 

example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  calc 
    n ^ 2 - 2 * n + 3 = (n - 1) ^ 2 + 2 := by ring 
    _ ≥ (5 - 1) ^ 2 + 2 := by rel [h1] 
    _ = 18 := by ring 
    _ > 14 := by numbers 

example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  calc 
    x ^ 2 - 2 * x = (x - 1) ^ 2 - 1 := by ring 
    _ ≥ -1 := by extra 

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
  calc 
    a ^ 2 + b ^ 2 = (a - b) ^ 2 + 2 * a * b := by ring 
    _ ≥ 2 * a * b := by extra 
