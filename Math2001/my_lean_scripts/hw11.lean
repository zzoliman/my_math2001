import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Mathlib.Tactic.Set
import Library.Tactic.ExistsDelaborator
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Mathlib.Tactic.GCongr
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Function

-- (a) Exercise 15 in [MoP, Subsection 8.1.13, Exercises].
/- 2 points -/
theorem problem4a : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  push_neg
  use fun x ↦ x
  dsimp [Surjective]
  constructor
  · intro y
    use y
    extra
  · push_neg
    use 1
    intro x
    intro h
    have hx := le_or_succ_le x 0
    obtain hl | hr :=  hx
    · have h_1 := calc
        1 = 2 * x := by rw [h]
        _ ≤ 2 * 0 := by rel [hl]
        _ = 0 := by ring
      contradiction
    · have h_2 := calc
        1 = 2 * x := by rw [h]
        _ ≥  2 * 1 := by rel [hr]
        _ = 2 := by ring
      contradiction

-- (b) Exercise 16 in [MoP, Subsection 8.1.13, Exercises].
/- 2 points -/
theorem problem4b : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  push_neg
  use 0
  dsimp [Surjective]
  push_neg
  use 1
  intro x
  ring
  numbers

-- (c) Exercise 17 in [MoP, Subsection 8.1.13, Exercises].
/- 3 points -/
theorem problem4c {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  dsimp [Injective]
  intro x y h
  obtain h1 | h2 | h3 := lt_trichotomy x y
  · have hh : f x < f y := by
      apply hf
      apply h1
    have h_cont := ne_of_lt hh
    contradiction
  · apply h2
  · have hh : f x > f y := by
      apply hf
      apply h3
    have h_cont := ne_of_gt hh
    contradiction

-- (d) Exercise 18 in [MoP, Subsection 8.1.13, Exercises].
/- 3 points -/
theorem problem4d {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp [Surjective]
  intro y
  simple_induction y with k IH
  . use x0
    rw [h0]
  . obtain ⟨x, hx⟩ := IH
    use i x
    rw [hi, hx]

-- (a) Exercise 1 in [MoP, Subsection 8.2.8, Exercises].
/- 2 points -/
theorem problem5a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  dsimp [Bijective]
  constructor
  · dsimp [Injective]
    intro x y h
    have h_eq : 3 * x = 3 * y := by addarith [h]
    cancel 3 at h_eq
  · dsimp [Surjective]
    intro y
    use (4 - y) / 3
    ring

-- (b) Exercise 2 in [MoP, Subsection 8.2.8, Exercises].
/- 2 points -/
theorem problem5b : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp [Bijective]
  push_neg
  left
  dsimp [Injective]
  push_neg
  use -2, 0
  ring
  numbers
  ring

-- (c) Exercise 2 in [MoP, Subsection 8.3.10, Exercises].
def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1) / 5

/- 3 points -/
theorem problem5c : Inverse u v := by
  dsimp [Inverse]
  constructor
  · ext x
    calc (v ∘ u) x = v (u x) := by rfl
      _ = (5 * x + 1 - 1) / 5 := by rfl
      _ = x := by ring
  · ext x
    calc
      (u ∘ v) x = u (v x) := by rfl
      _ = 5 * ((x - 1) / 5) + 1 := by rfl
      _ = x := by ring

-- (d) Exercise 3 in [MoP, Subsection 8.3.10, Exercises].
/- 3 points -/
theorem problem5d {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp [Injective] at *
  intro c1 c2 h_comp
  apply hf
  apply hg
  apply h_comp
