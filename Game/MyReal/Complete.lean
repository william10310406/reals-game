import Game.Levels.RealLimits

/-!
# Cauchy sequences of reals

* `IsCauchy a` (for `a : ℕ → ℝ`): for every `k` there is `N` with `abs (a m - a n) ≤ eps k`
  for all `m, n ≥ N`.
* `ratSeq q` is the sequence `ofRat (q 0), ofRat (q 1), …` of reals.
* The tactic `choose f hf using h` turns `h : ∀ n, ∃ y, P n y` into a function `f` with
  `hf : ∀ n, P n (f n)`. It uses Lean's axiom of choice (`Classical.axiomOfChoice`).
  Completeness of the Cauchy reals needs (countable) choice: we must pick a rational near
  each term `a n`.
-/

namespace MyReal

/-- `a` is a Cauchy sequence of reals: its terms get as close together as you want. -/
def IsCauchy (a : MyNat → MyReal) : Prop :=
  ∀ k : MyNat, ∃ N : MyNat, ∀ m n : MyNat, N ≤ m → N ≤ n → abs (a m - a n) ≤ eps k

/-- The sequence `ofRat (q 0), ofRat (q 1), …` of reals. -/
noncomputable def ratSeq (q : MyNat → MyRat) : MyNat → MyReal := fun n => ofRat (q n)

theorem ratSeq_apply (q : MyNat → MyRat) (n : MyNat) : ratSeq q n = ofRat (q n) := rfl

end MyReal

/-- `choose f hf using h` turns `h : ∀ n, ∃ y, P n y` into `f` and `hf : ∀ n, P n (f n)`. -/
syntax (name := chooseUsing) "choose " ident ppSpace ident " using " term : tactic

macro_rules
  | `(tactic| choose $f:ident $hf:ident using $h:term) =>
    `(tactic| obtain ⟨$f, $hf⟩ := Classical.axiomOfChoice $h)
