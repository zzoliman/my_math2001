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

def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by
  simple_induction n with n IH
  · rw [c]; dsimp [Odd]; use 3; numbers
  · rw [c] at *; dsimp [Odd] at *
    obtain ⟨a,IHa⟩ := IH
    use 3 * a - 4
    rw [IHa]; ring

example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with n IH
  · simp
  · rw [c]; rw [IH]; ring

def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with n IH
  · rw [y]; simp
  · rw [y]; rw [IH]; ring

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

example (n : ℕ) : 0 < n ! := by
  simple_induction n with n IH
  · simp
  · rw [factorial]
    have H : 0 < n + 1 := by simp
    simp; apply IH

example {n : ℕ} (hn : 2 ≤ n) : Nat.Even (n !) := by
  induction_from_starting_point n, hn with n hn IH
  · dsimp [Nat.Even]; use 1; simp
  · dsimp [Nat.Even] at *
    obtain ⟨a,IH⟩ := IH
    use n * a + a
    rw [factorial,IH]; ring

def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with n IH1 IH2
  · simp
  · simp
  · rw [b,IH1,IH2]; ring

def c' : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c' n

example (n : ℕ) : c' n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with n IH1 IH2
  · simp
  · simp
  · rw [c',IH1]; ring

def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with n IH1 IH2
  · simp
  · simp
  · rw[t,IH1,IH2]; ring
