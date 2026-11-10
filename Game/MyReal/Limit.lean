import Game.Levels.Inequalities

/-!
# Limits of sequences of rationals

`Tendsto s L`: for every `k` there is `N` with `s n - L ≤ 1/(k+1)` and `L - s n ≤ 1/(k+1)`
for all `n ≥ N`. This is exactly `Close s (const L)` (theorem `tendsto_iff_close`).
-/

namespace MyRat

/-- `s` tends to `L`: the terms get as close to `L` as you want. -/
def Tendsto (s : MyNat → ℚ) (L : ℚ) : Prop :=
  ∀ k : MyNat, ∃ N : MyNat, ∀ n : MyNat, N ≤ n →
    s n - L ≤ frac 1 (MyNat.succ k) ∧ L - s n ≤ frac 1 (MyNat.succ k)

theorem tendsto_iff_close (s : MyNat → ℚ) (L : ℚ) : Tendsto s L ↔ Close s (const L) := Iff.rfl

/-- The sequence `1/1, 1/2, 1/3, ...`. -/
def invSucc : MyNat → ℚ := fun n => frac 1 (MyNat.succ n)

theorem invSucc_apply (n : MyNat) : invSucc n = frac 1 (MyNat.succ n) := rfl

end MyRat
