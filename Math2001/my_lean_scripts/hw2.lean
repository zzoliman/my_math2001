import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

--Problem 5
-- c : Translate as closely as you can your natural deduction in part (a) into a LEAN_4.script
example {p q : Prop} : (¬p ∧ ¬q) → ¬(p ∨ q) := by
  intro h
  have h_bot : p ∨ q → ⊥ := by
  {
    intro h_porq
    have h_bot_1 : p → ⊥ := by
    {
      intro h_p
      have neg_p : ¬p := And.left h
      apply neg_p h_p
    } 
    have h_bot_2 : q → ⊥ := by
    {
      intro h_q
      have neg_q : ¬q := And.right h
      apply neg_q h_q
    } 
    apply Or.elim h_porq h_bot_1 h_bot_2
  }
  apply h_bot

-- d : Translate as closely as you can your natural deduction in part (b) into a LEAN_4.script
example {p q : Prop} : (¬p ∨ ¬q) → ¬(p ∧ q) := by
  intro h
  have h1 : ¬p → ¬(p ∧ q) := by
  {
    intro h_not_p
    have neg_pq : ¬(p ∧ q) := by
    {
      intro h_pq
      have h_p : p := And.left h_pq
      apply h_not_p h_p
    }
    apply neg_pq
  } 
  have h2: ¬q → ¬(p ∧ q) := by
  {
    intro h_not_q
    have neg_pq: ¬(p ∧ q) := by
    {
      intro h_pq
      have h_q : q := And.right h_pq
      apply h_not_q h_q
    }
    apply neg_pq
  }
  apply Or.elim h h1 h2
  
-- Problem 6
-- a
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 := by
  have h3 :=
  calc
    x + 3 ≥ 2 * y := by rel [h1]
    _ ≥ 2 * 1 := by rel [h2]
    _ = 2 := by numbers
  addarith [h3]

-- b
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 := by
  calc
    a + b = ((a) + (a + 2 * b)) / 2 := by ring
    _ ≥ (3 + 4) / 2 := by rel [h1, h2]
    _ = 7/2 := by ring
    _ ≥ 3 := by numbers

-- c
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