import Game.Levels.Rationals

/-!
# Sequences of rationals

A sequence is a function `ℕ → ℚ`. We measure "small" with the numbers `frac 1 (succ k)`,
that is `1/(k+1)`. So we never need `<` or absolute values:

* `IsCauchy s`: for every `k` there is `N` with `s m - s n ≤ 1/(k+1)` for all `m n ≥ N`.
  (Swapping `m` and `n` gives the other sign, so this is the usual definition.)
* `Close s t`: for every `k` there is `N` with `s n - t n ≤ 1/(k+1)` and `t n - s n ≤ 1/(k+1)`
  for all `n ≥ N`.
-/

namespace MyRat

/-- The constant sequence `c, c, c, ...`. -/
def const (c : ℚ) : MyNat → ℚ := fun _ => c

theorem const_apply (c : ℚ) (n : MyNat) : const c n = c := rfl

/-- The sequence `s 0 + t 0, s 1 + t 1, ...`. -/
def addSeq (s t : MyNat → ℚ) : MyNat → ℚ := fun n => s n + t n

theorem addSeq_apply (s t : MyNat → ℚ) (n : MyNat) : addSeq s t n = s n + t n := rfl

/-- `s` is a Cauchy sequence: its terms get as close together as you want. -/
def IsCauchy (s : MyNat → ℚ) : Prop :=
  ∀ k : MyNat, ∃ N : MyNat, ∀ m n : MyNat, N ≤ m → N ≤ n → s m - s n ≤ frac 1 (MyNat.succ k)

/-- `s` and `t` are close: their terms get as close together as you want. -/
def Close (s t : MyNat → ℚ) : Prop :=
  ∀ k : MyNat, ∃ N : MyNat, ∀ n : MyNat, N ≤ n →
    s n - t n ≤ frac 1 (MyNat.succ k) ∧ t n - s n ≤ frac 1 (MyNat.succ k)

end MyRat
