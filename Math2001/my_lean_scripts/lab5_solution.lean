import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat

/- 3.1 -/

example : Odd (-9 : ℤ) := by
  use -5 
  simp 

example : Even (26 : ℤ) := by
  use 13 
  simp 

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  dsimp [Odd] at * 
  dsimp [Even] at hn 
  obtain ⟨a, ha⟩ := hm 
  obtain ⟨b, hb⟩ := hn 
  use a + b 
  rw [ha, hb] 
  ring 

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  dsimp [Odd] at * 
  dsimp [Even] at hq 
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq 
  use a - b - 2 
  rw [ha, hb] 
  ring 

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  dsimp [Even] at * 
  dsimp [Odd] at hb 
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb 
  use 3 * p + q - 1 
  rw [hp, hq] 
  ring 

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  dsimp [Odd] at * 
  dsimp [Even] 
  obtain ⟨a, ha⟩ := hr 
  obtain ⟨b, hb⟩ := hs 
  use 3 * a - 5 * b - 1 
  rw[ha, hb] 
  ring 

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  dsimp [Odd] at * 
  obtain ⟨k, hk⟩ := hx 
  use 4 * k ^ 3 + 6 * k ^ 2 + 3 * k 
  rw [hk] 
  ring 

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  dsimp [Odd] at hn 
  dsimp [Even] 
  obtain ⟨k, hk⟩ := hn 
  use 2 * k ^ 2 - k 
  rw [hk] 
  ring 

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  dsimp [Odd] at * 
  obtain ⟨b, hb⟩ := ha 
  use 2 * b ^ 2 + 4 * b - 1 
  rw [hb] 
  ring 

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  dsimp [Odd] at * 
  obtain ⟨a, ha⟩ := hp 
  use 2 * a ^ 2 + 5 * a - 1 
  rw [ha] 
  ring 

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  dsimp [Odd] at * 
  obtain ⟨a, ha⟩ := hx 
  obtain ⟨b, hb⟩ := hy 
  use 2 * a * b + a + b 
  rw [ha,hb] 
  ring 

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  dsimp [Odd] 
  obtain hn | hn := Int.even_or_odd n 
  · dsimp [Even] at hn
    obtain ⟨a,ha⟩ := hn 
    rw [ha] 
    use 6 * a ^ 2 + 3 * a - 1 
    ring 
  · dsimp [Odd] at hn 
    obtain ⟨a,ha⟩ := hn 
    rw [ha] 
    use 6 * a ^ 2 + 9 * a + 2 
    ring 

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  obtain hn | hn := Int.even_or_odd n 
  · dsimp [Even] at hn 
    obtain ⟨k, hk⟩ := hn 
    use 2 * k + 1 
    constructor 
    · rw [hk] 
      extra 
    · dsimp [Odd] 
      use k 
      ring 
  · dsimp [Odd] at hn 
    obtain ⟨k, hk⟩ := hn 
    use 2 * k + 3 
    constructor 
    · rw [hk] 
      simp 
    · dsimp [Odd] 
      use k + 1 
      ring 


/- 4.1 -/

example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by 
  have H : a ≥ -3 + 4 * 2 - 2 ^ 2 := h 2
  calc 
    a ≥ -3 + 4 * 2 - 2 ^ 2 := by rel [H] 
    _ = 1 := by ring 

example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  use 0 
  intros m 
  extra 

example : ¬(Prime 45) := by
  apply not_prime 5 9 
  · numbers 
  · numbers 
  · numbers 

/- 4.2 -/

example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor 
  · intros h 
    have h1 : 2 * x = 2 * 6 := 
    calc 
      2 * x = 2 * x - 1 + 1 := by ring 
      _ = 11 + 1 := by rw [h] 
      _ = 2 * 6 := by ring 
    cancel 2 at h1 
  · intros h 
    calc 
      2 * x - 1 = 2 * 6 - 1 := by rw [h] 
      _ = 11 := by ring 

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor 
  · intros h 
    dsimp [(.∣.)] at * 
    obtain ⟨c,hc⟩ := h 
    constructor 
    · use 9 * c 
      calc 
        n = 63 * c := by rw [hc] 
        _ = 7 * (9 * c) := by ring 
    · use 7 * c 
      calc 
        n = 63 * c := by rw [hc] 
        _ = 9 * (7 * c) := by ring 
  · intros h 
    dsimp [(.∣.)] at * 
    obtain ⟨h1,h2⟩ := h 
    obtain ⟨k1,hk1⟩ := h1 
    obtain ⟨k2,hk2⟩ := h2 
    use 4 * k2 - 3 * k1 
    calc 
      n = 28 * n - 27 * n := by ring 
      _ = 4 * 7 * n + (-3) * 9 * n := by ring 
      _ = 4 * 7 * (n) + (-3) * 9 * (7 * k1) := by rw [hk1] 
      _ = 4 * 7 * (9 * k2) + (-3) * 9 * (7 * k1) := by rw [hk2] 
      _ = 63 * (4 * k2 - 3 * k1) := by ring 

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor 
  · intros h 
    rw [Int.ModEq] 
    dsimp [(.∣.)] at * 
    obtain ⟨c,hc⟩ := h 
    use c 
    addarith [hc] 
  · intros h 
    rw [Int.ModEq] at h 
    simp at h 
    apply h 

example {a b : ℤ} (hab : a ∣ b) : a ∣ 3 * b ^ 3 - b ^ 2 + 5 * b := by
  dsimp [(.∣.)] at * 
  obtain ⟨c,habc⟩ := hab 
  use 3 * b ^ 2 * c - b * c + 5 * c 
  rw [habc] 
  ring 

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor 
  · intros h 
    have H1 := le_or_gt k 0
    obtain H1 | H1 := H1 
    · left 
      simp at H1 
      apply H1 
    · right 
      have H2 := le_or_gt k 1 
      obtain H2 | H2 := H2 
      · left 
        have H3 : k ≥ 1 := by addarith [H1] 
        apply le_antisymm H2 H3 
      · right 
        have H3 : k ≥ 2 := by addarith [H2] 
        have H4 : ¬(k ≥ 3) := by 
          intros H5 
          have H6 : 3 * 2 ≥ 3 * k := 
          calc 
            3 * 2 = 6 := by ring 
            _ ≥ k ^ 2 := by rel[h] 
            _ = k * k := by ring 
            _ ≥ 3 * k := by rel [H5] 
          cancel 3 at H6 
          have H7 : k = 2 := le_antisymm H6 H3 
          addarith [H5,H7] 
        simp at H4 
        addarith [H3,H4] 
  · intros h 
    obtain h1 | h2 | h3 := h 
    · rw [h1] 
      numbers 
    · rw [h2] 
      numbers 
    · rw [h3] 
      numbers 
