import Mathlib

def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

theorem ArchProp {ε : ℝ} (_hε : ε > 0) : ∃ N : ℕ, 1 / ε < N :=
  exists_nat_gt (1 / ε)          -- Mathlib: ∀ x, ∃ n : ℕ, x < n

theorem simple1nLim (a : ℕ → ℝ) (ha : ∀ n, a n = (n + 1) / n) : ∃ L, SeqLim a L := by
  use 1
  rw [SeqLim]
  intro ε _hε
  obtain ⟨N, hN⟩ := ArchProp _hε
  use N
  intro n hn
  specialize ha n
  rw [ha]
  have f00 : 1/ε > 0 := by positivity

  have hn' : (n : ℝ) ≥ N := by exact_mod_cast hn
  have f0 : (n:ℝ) > 0 := by linarith [hn', hN, f00]

  have f1 : (↑n + 1) / ↑n - 1 = 1/(n:ℝ) := by
    field_simp
    ring

  rw [f1, abs_of_pos (by positivity)]

  field_simp
  field_simp at hN
  have h2 : ε * N ≤ ε * n := mul_le_mul_of_nonneg_left hn' _hε.le
  linarith
