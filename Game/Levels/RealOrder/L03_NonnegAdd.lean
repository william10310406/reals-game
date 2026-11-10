import Game.Levels.RealOrder.L02_LeRefl

World "RealOrder"
Level 3
Title "Sums of nonnegative reals"

namespace MyReal

open MyNat (succ)

Introduction "
If `x ≥ 0` and `y ≥ 0`, then `x + y ≥ 0`.
The trick from the Reals world: ask both hypotheses for half of `1/(k+1)`.
"

/-- If $x \ge 0$ and $y \ge 0$, then $x + y \ge 0$. -/
Statement nonneg_add (x y : ℝ) : nonneg x → nonneg y → nonneg (x + y) := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  obtain ⟨t, ht, rfl⟩ := exists_ofSeq y
  intro hx hy
  rw [nonneg_ofSeq] at hx hy
  rw [ofSeq_add, nonneg_ofSeq]
  intro k
  Hint "Ask for half: `obtain ⟨N1, h1⟩ := {hx} (succ k + k)`, and the same with `{hy}`."
  Branch
    obtain ⟨N1, h1⟩ := hx k
    Hint "With `k` you get `-1/(k+1)` for each term, so `-2/(k+1)` for the sum: too much.
    Ask for half instead: `{hx} (succ k + k)`."
  obtain ⟨N1, h1⟩ := hx (succ k + k)
  obtain ⟨N2, h2⟩ := hy (succ k + k)
  use N1 + N2
  intro n hn
  have hn1 : N1 ≤ n := MyNat.le_trans N1 (N1 + N2) n (MyNat.le_add_right N1 N2) hn
  rw [MyNat.add_comm] at hn
  have hn2 : N2 ≤ n := MyNat.le_trans N2 (N2 + N1) n (MyNat.le_add_right N2 N1) hn
  Hint "Compute the term and split the bound into halves:
  `rw [MyRat.addSeq_apply, ← MyRat.half (succ k) (MyNat.succ_ne_zero k), MyNat.add_succ, MyRat.neg_add]`."
  rw [MyRat.addSeq_apply, ← MyRat.half (succ k) (MyNat.succ_ne_zero k), MyNat.add_succ,
    MyRat.neg_add]
  Hint "Add the two inequalities with `MyRat.add_le_add`."
  exact MyRat.add_le_add _ _ _ _ (h1 n hn1) (h2 n hn2)

Conclusion "
Sums of nonnegative reals are nonnegative.
"

TheoremTab "≤ℝ"

end MyReal
