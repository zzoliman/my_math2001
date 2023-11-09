import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Theory.Comparison
import Library.Theory.Prime
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

-- (a) Exercise 4 in [MoP, Subsection 6.2.7, Exercises].
def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

theorem problem4a (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  -- obtain ⟨a, ha⟩ := IH
  · dsimp [B]
    numbers
  · calc
      B (k + 1) = B k + (↑k + 1) ^ 2 := by rw [B]
      _ = ↑k * (↑k + 1) * (2 * ↑k + 1) / 6 + (↑k + 1) ^ 2 := by rw [IH]
      _ = (↑k + 1) * (↑k + 1 + 1) * (2 * (↑k + 1) + 1) / 6 := by ring


-- (b) Exercise 5 in [MoP, Subsection 6.2.7, Exercises].
def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

theorem problem4b (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH
  · dsimp [S]
    numbers
  · calc
      S (k + 1) = S k + 1 / 2 ^ (k + 1) := by rw [S]
      _ = (2 - 1 / 2 ^ k) + 1 / 2 ^ (k + 1) := by rw [IH]
      _ = 2 - 1 / 2 ^ (k + 1) := by ring


-- (c) Use the result from part (b) to prove in Lean 4 that Sn ⩽ 2 for all n ∈ N.
/- 3 points -/
theorem problem4c (n : ℕ) : S n ≤ 2 := by
  rw [problem4b]
  have h1 : (1 / 2 ^ n:ℚ) ≥ 0 := by extra
  have h2 : -(1 / 2 ^ n:ℚ) ≤ 0 := by addarith [h1]
  calc
    2 - (1 / 2 ^ n:ℚ) ≤ 2 := by addarith [h2]

-- (d) Exercise 8 in [MoP, Subsection 6.2.7, Exercises].
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

theorem problem4d (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  simple_induction n with k IH
  · dsimp [factorial]
    numbers
  · have h1 : (k + 1 + 1) ≥ (k + 1) := by extra
    have h2 : (k + 2) ^ k ≥ (k + 1) ^ k := by rel [h1]
    calc
      (k + 1 + 1)! = (k + 1 + 1) * (k + 1)! := by rw [factorial] -- order matters
      _ ≤ (k + 2) * (k + 1) ^ k := by rel [IH]
      _ ≤ (k + 2) * (k + 2) ^ k := by rel [h2]
      _ = (k + 2) ^ (k + 1) := by ring

-- (a) Exercise 4 in [MoP, Subsection 6.3.6, Exercises].
def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

theorem problem5a (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  · dsimp [q]
    numbers
  · dsimp [q]
    numbers
  · calc
      q (k + 1 + 1) = 2 * q (k + 1) - q k + 6 * k + 6 := by rw [q]
      _ = 2 * ((↑k + 1) ^ 3 + 1) - (↑k ^ 3 + 1) + 6 * k + 6 := by rw [IH1, IH2]
      _ = (↑k + 1 + 1) ^ 3 + 1 := by ring

-- (b) Exercise 7 in [MoP, Subsection 6.3.6, Exercises].
def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

theorem problem5b : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  use 7
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · dsimp [r]
    numbers
  · dsimp [r]
    numbers
  · calc
      r (k + 1 + 1) = 2 * r (k + 1) + r k := by rw [r]
      _ ≥ 2 * 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
      _ = 2 ^ (k + 1 + 1) + 2 ^ k := by ring
      _ ≥ 2 ^ (k + 1 + 1) := by extra

-- (c) Exercise 1 in [MoP, Subsection 6.4.3, Exercises]. □
theorem problem5c (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain h_even | h_odd := Nat.even_or_odd n
  · obtain ⟨m, hm⟩ := h_even
    rw [hm] at hn
    cancel 2 at hn
    obtain IH := problem5c m hn
    obtain ⟨a, x, hx, hp⟩ := IH
    use a + 1, x
    constructor
    · apply hx
    · calc
        n = 2 * m := by rw [hm]
        _ = 2 * (2 ^ a * x) := by rw [hp]
        _ = 2 ^ (a + 1) * x := by ring
  · use 0
    use n
    constructor
    · apply h_odd
    · ring
