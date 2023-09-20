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