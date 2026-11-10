import Game.Levels.Limits.L04_TendstoOfClose

World "Limits"
Level 5
Title "Convergent means Cauchy"

namespace MyRat

open MyNat (succ)

Introduction "
If the terms get close to `L`, they get close to each other.
Ask for half of `1/(k+1)`, and split `s m - s n` at `L`.
"

/-- A convergent sequence is Cauchy. -/
Statement cauchy_of_tendsto (s : ℕ → ℚ) (L : ℚ) : Tendsto s L → IsCauchy s := by
  intro h k
  Hint "Ask for half: `obtain ⟨N, hN⟩ := {h} (succ k + k)`."
  obtain ⟨N, hN⟩ := h (succ k + k)
  use N
  intro m n hm hn
  obtain ⟨a1, a2⟩ := hN m hm
  obtain ⟨b1, b2⟩ := hN n hn
  Hint "Split into halves and split `s m - s n` at `L`:
  `rw [← half (succ k) (MyNat.succ_ne_zero k), MyNat.add_succ, ← sub_add_sub (s n) L (s m)]`."
  rw [← half (succ k) (MyNat.succ_ne_zero k), MyNat.add_succ, ← sub_add_sub (s n) L (s m)]
  exact add_le_add _ _ _ _ a1 b2

Conclusion "
Every convergent sequence of rationals is Cauchy, so it is a real number.
"

TheoremTab "lim"

end MyRat
