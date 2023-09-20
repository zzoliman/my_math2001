import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

--page 21 of Lecture Slides 02

example {P Q R : Prop} (h : (P ∧ Q) → R) : P → (Q → R) := by 
  intro p
  intro q
  have pq : P ∧ Q := And.intro p q 
  apply h pq


--page 23 of Lecture Slides 02

example {P Q R : Prop} (h : P → (Q → R)) : (P → Q) → (P → R) := 
  have pq_pr : (P → Q) → (P → R) := by
    intros pq 
    have pr : P → R := by
      intros p
      have q : Q := (pq p) 
      have qr : Q → R := (h p) 
      have r : R := (qr q) 
      apply r
    apply pr
  by apply pq_pr

--page 24 of Lecture Slides 02

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p

example {P Q R : Prop} (h1 : (P ∧ ¬Q) → R) (h2 : ¬R) (h3 : P) : Q := by
  have nnq : ¬¬Q := by
    intros nq 
    have p_nq : P ∧ ¬Q := And.intro h3 nq 
    have r : R := (h1 p_nq) 
    have r_nr : R ∧ ¬R := And.intro r h2
    apply h2 r 
  apply notnotE nnq 

--Exercises from MacBeth

--Example 1.3.1

example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2] 
    _ = 11 := by ring

--Example 1.3.2

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc 
    x = x + 4 - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

--Example 1.3.3

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = a - 5 * b + 5 * b := by ring 
    _ = 4 + 5 * b := by rw [h1] 
    _ = -6 + 5 * (b + 2) := by ring 
    _ = -6 + 5 * 3 := by rw [h2] 
    _ = 9 := by ring
