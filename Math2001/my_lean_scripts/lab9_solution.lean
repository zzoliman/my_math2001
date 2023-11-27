import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Addarith
import Library.Tactic.Induction
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
set_option linter.unusedVariables false

namespace Nat

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with n IH
  · simp
  · calc
      3 ^ (n + 1) = 3 * 3 ^ n := by ring
      _ ≥ 3 * (n ^ 2 + n + 1) := by rel [IH]
      _ = 3 * n ^ 2 + 3 * n + 3 := by ring
      _ = 2 * n ^ 2 + n ^ 2 + 3 * n + 3 := by ring
      _ ≥ n ^ 2 + 3 * n + 3 := by extra
      _ = (n + 1) ^ 2 + (n + 1) + 1 := by ring

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with n IH
  · left; simp; dsimp [Int.ModEq]; simp
  · obtain IH | IH := IH
    · right
      dsimp [Int.ModEq,(.∣.)] at *
      obtain ⟨c,IH⟩ := IH
      use 5 * c
      symm
      calc
        8 * (5 * c) = 5 * (8 * c) := by ring
        _ = 5 * (5 ^ n - 1) := by rw [IH]
        _ = 5 ^ (n + 1) - 5 := by ring
    · left
      dsimp [Int.ModEq,(.∣.)] at *
      obtain ⟨c,IH⟩ := IH
      use 5 * c + 3
      symm
      calc
        8 * (5 * c + 3) = 5 * (8 * c) + 24 := by ring
        _ = 5 * (5 ^ n - 5) + 24 := by rw [IH]
        _ = 5 ^ (n + 1) - 1 := by ring

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with n IH
  · left
    dsimp [Int.ModEq,(.∣.)]
    use 0
    simp
  · obtain IH | IH := IH
    · right
      dsimp [Int.ModEq,(.∣.)] at *
      obtain ⟨k,IH⟩ := IH
      use 6 * k
      symm
      calc
        7 * (6 * k) = 6 * (7 * k) := by ring
        _ = 6 * (6 ^ n - 1) := by rw [IH]
        _ = 6 ^ (n + 1) - 6 := by ring
    · left
      dsimp[Int.ModEq,(.∣.)] at *
      obtain ⟨k,IH⟩ := IH
      use 6 * k + 5
      symm
      calc
        7 * (6 * k + 5) = 6 * (7 * k) + 35 := by ring
        _ = 6 * (6 ^ n - 6) + 35 := by rw [IH]
        _ = 6 ^ (n + 1) - 1 := by ring

example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with n IH
  · left; simp; dsimp [Int.ModEq,(.∣.)]; use 0; simp
  · obtain IH | IH | IH := IH
    · right; right; dsimp [Int.ModEq,(.∣.)] at *
      obtain ⟨k,IH⟩ := IH
      use 4 * k; symm
      calc
        7 * ( 4 * k) = 4 * (7 * k) := by ring
        _ = 4 * (4 ^ n - 1) := by rw [IH]
        _ = 4 ^ (n + 1) - 4 := by ring
    · left; dsimp [Int.ModEq,(.∣.)] at *
      obtain ⟨k,IH⟩ := IH
      use 4 * k + 1; symm
      calc
        7 * (4 * k + 1) = 4 * (7 * k) + 7 := by ring
        _ = 4 * (4 ^ n - 2) + 7 := by rw [IH]
        _ = 4 ^ (n + 1) - 1 := by ring
    · right; left; dsimp [Int.ModEq,(.∣.)] at *
      obtain ⟨k,IH⟩ := IH
      use 4 * k + 2; symm
      calc
        7 * (4 * k + 2) = 4 * (7 * k) + 14 := by ring
        _ = 4 * (4 ^ n - 4) + 14 := by rw [IH]
        _ = 4 ^ (n + 1) - 2 := by ring

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5
  intros x hx
  induction_from_starting_point x, hx with n hn IH
  · simp
  · calc
      2 ^ (n + 1) = 2 * 2 ^ n := by ring
      _ ≥ 2 * (n ^ 2 + 4) := by rel [IH]
      _ = n ^ 2 + n * n + 8 := by ring
      _ ≥ n ^ 2 + 5 * n + 8 := by rel [hn]
      _ = (n + 1) ^ 2 + 4 + 3 * n + 3 := by ring
      _ ≥ (n + 1) ^ 2 + 4 + 3 * 5 + 3 := by rel [hn]
      _ = (n + 1) ^ 2 + 4 + 18 := by ring
      _ ≥ (n + 1) ^ 2 + 4 := by extra

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10
  intros x hx
  induction_from_starting_point x, hx with n hn IH
  · simp
  · calc
      2 ^ (n + 1) = 2 * 2 ^ n := by ring
      _ ≥ 2 * (n ^ 3) := by rel [IH]
      _ = n ^ 3 + n * n ^ 2 := by ring
      _ ≥ n ^ 3 + 10 * n ^ 2 := by rel [hn]
      _ = n ^ 3 + 3 * n ^ 2 + 7 * n * n := by ring
      _ ≥ n ^ 3 + 3 * n ^ 2 + 7 * 10 * n := by rel [hn]
      _ = n ^ 3 + 3 * n ^ 2 + 3 * n + 67 * n := by ring
      _ ≥ n ^ 3 + 3 * n ^ 2 + 3 * n + 67 * 10 := by rel [hn]
      _ = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 + 669 := by ring
      _ = (n + 1) ^ 3 + 669 := by ring
      _ ≥ (n + 1) ^ 3 := by extra

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  dsimp [Odd] at *
  obtain ⟨b,hb⟩ := ha
  simple_induction n with n IH
  · simp
  · obtain ⟨c,hc⟩ := IH
    use 2 * b * c + b + c
    calc
      a ^ (n + 1) = a * a ^ n := by ring
      _ = (2 * b + 1) * a ^ n := by rw [hb]
      _ = (2 * b + 1) * (2 * c + 1) := by rw [hc]
      _ = 2 * (2 * b * c + b + c) + 1 := by ring

theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  contrapose ha
  rw [← odd_iff_not_even] at *
  apply Odd.pow
  apply ha
