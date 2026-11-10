import Game.Levels.RealOrder.L19_RatAbsAdd

World "RealOrder"
Level 20
Title "Nonnegative terms"

namespace MyReal

open MyNat (succ)

Introduction "
If the terms of `s` are `≥ 0` from some `N` on, then `ofSeq s hs ≥ 0`.
"

/-- If $s_n \ge 0$ for all $n \ge N$, then the real of $s$ is $\ge 0$. -/
Statement nonneg_of_eventually (s : ℕ → ℚ) (hs : MyRat.IsCauchy s) :
    (∃ N, ∀ n, N ≤ n → MyRat.nonneg (s n)) → nonneg (ofSeq s hs) := by
  intro h
  obtain ⟨N, hN⟩ := h
  rw [nonneg_ofSeq]
  intro k
  use N
  intro n hn
  Hint "First `have h0 : 0 ≤ s n := by …`. Inside: `rw [MyRat.le_iff_nonneg, MyRat.sub_eq_add_neg,
  MyRat.neg_zero, MyRat.add_zero]`, then `exact hN n hn`."
  have h0 : 0 ≤ s n := by
    rw [MyRat.le_iff_nonneg, MyRat.sub_eq_add_neg, MyRat.neg_zero, MyRat.add_zero]
    exact hN n hn
  Hint "Chain through `0`: `MyRat.le_trans _ 0 _ (MyRat.neg_eps_le k) {h0}`."
  exact MyRat.le_trans _ 0 _ (MyRat.neg_eps_le k) h0

Conclusion "
For all terms, use `use 0` for the `N`.
"

TheoremTab "≤ℝ"

end MyReal
