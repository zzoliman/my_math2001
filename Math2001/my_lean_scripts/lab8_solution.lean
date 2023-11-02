import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.Numbers
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
set_option push_neg.use_distrib true

example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor 
  · by_cases P 
    · intros np 
      apply h 
    · intros nnp 
      contradiction 
  · intros p np 
    contradiction   

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor 
  · intros h1
    by_cases (∃ x, ¬P x)
    · apply h 
    · rw [not_exists] at h 
      have h2 : ∀ (x : α), P x := by 
        intros x 
        have nnpx : ¬¬P x := h x
        rw [not_not] at nnpx 
        apply nnpx 
      contradiction 
  · intros h1 h2
    obtain ⟨x,hx⟩ := h1 
    apply hx 
    apply h2 

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by 
  constructor 
  · intros h1 
    rw [not_forall] at h1 
    obtain ⟨a,h1⟩ := h1 
    rw [not_forall] at h1 
    obtain ⟨b,h1⟩ := h1 
    simp at h1 
    obtain ⟨h1,h2⟩ := h1 
    rw [not_or] at h2 
    obtain ⟨h2,h3⟩ := h2 
    simp at * 
    use a,b
    apply And.intro h1 (And.intro h2 h3) 
  · intros h1 h2 
    obtain ⟨a,b,hab⟩ := h1 
    have contra : a * b = 1 → a = 1 ∨ b = 1 := (h2 a b) 
    rw [← not_or, ← not_imp] at hab 
    contradiction 

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) := by 
  constructor 
  · intros h1 x
    rw [not_exists] at h1 
    have h2 : ¬∀ (y : ℝ), y ≤ x := h1 x 
    rw [not_forall] at h2 
    obtain ⟨y,h2⟩ := h2 
    use y 
    simp at h2 
    apply h2 
  · intros h1 h2 
    obtain ⟨x,h2⟩ := h2 
    have h3 : ∃ y, y > x := h1 x 
    obtain ⟨y,h3⟩ := h3 
    have h4 : y ≤ x := h2 y 
    rw [← not_lt] at h4 
    contradiction 

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by 
  constructor 
  · intros h1 m 
    rw [not_exists] at h1 
    have h2 : ¬∀ (n : ℤ), m = n + 5 := h1 m 
    rw [not_forall] at h2 
    obtain ⟨n,h2⟩ := h2 
    use n 
    simp 
    apply h2 
  · intros h1 h2 
    obtain ⟨m,h2⟩ := h2 
    have h3 : ∃ n, m ≠ n + 5 := h1 m 
    simp at h3 
    obtain ⟨n,h3⟩ := h3 
    have h4 : m = n + 5 := h2 n 
    contradiction 

example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 1/2 
  numbers 