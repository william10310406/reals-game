import Game.Levels.RealIneq

/-!
# Sequences of reals and their limits

* `eps k` is the real `1/(k+1)` (rule `eps_def`).
* `const c` is the constant sequence, `addSeq a b` the sum of two sequences of reals.
* `Tendsto a L`: for every `k` there is `N` with `abs (a n - L) ≤ eps k` for all `n ≥ N`.

This is the textbook definition `∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε`, with `ε` running
through `1/(k+1)`. By the Archimedean property both say the same, and this one avoids
division in `ℝ`. No plumbing is needed here: these are plain definitions.
-/

namespace MyReal

open MyNat (succ)

/-- The real number `1/(k+1)`. -/
noncomputable def eps (k : MyNat) : MyReal := ofRat (MyRat.frac 1 (succ k))

theorem eps_def (k : MyNat) : eps k = ofRat (MyRat.frac 1 (succ k)) := rfl

/-- The constant sequence `c, c, c, …` of reals. -/
def const (c : MyReal) : MyNat → MyReal := fun _ => c

theorem const_apply (c : MyReal) (n : MyNat) : const c n = c := rfl

/-- The sequence `a 0 + b 0, a 1 + b 1, …` of reals. -/
def addSeq (a b : MyNat → MyReal) : MyNat → MyReal := fun n => a n + b n

theorem addSeq_apply (a b : MyNat → MyReal) (n : MyNat) : addSeq a b n = a n + b n := rfl

/-- `a` tends to `L`: in the end, `abs (a n - L) ≤ 1/(k+1)`, for every `k`. -/
def Tendsto (a : MyNat → MyReal) (L : MyReal) : Prop :=
  ∀ k : MyNat, ∃ N : MyNat, ∀ n : MyNat, N ≤ n → abs (a n - L) ≤ eps k

attribute [irreducible] eps

end MyReal
