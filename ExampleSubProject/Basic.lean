import Mathlib

example (a b : ℕ) : a + b = b + a := by
  exact Nat.add_comm a b

#eval 2 + 2
