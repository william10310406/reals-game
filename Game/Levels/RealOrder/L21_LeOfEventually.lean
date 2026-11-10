import Game.Levels.RealOrder.L20_NonnegOfEventually

World "RealOrder"
Level 21
Title "Comparing terms"

namespace MyReal

Introduction "
If `s n ≤ t n` from some `N` on, then `ofSeq s hs ≤ ofSeq t ht`.
"

/-- If $s_n \le t_n$ for all $n \ge N$, then the real of $s$ is $\le$ the real of $t$. -/
Statement le_of_eventually (s t : ℕ → ℚ) (hs : MyRat.IsCauchy s) (ht : MyRat.IsCauchy t) :
    (∃ N, ∀ n, N ≤ n → s n ≤ t n) → ofSeq s hs ≤ ofSeq t ht := by
  intro h
  obtain ⟨N, hN⟩ := h
  Hint "`rw [le_iff_nonneg, sub_eq_add_neg, ofSeq_neg, ofSeq_add]`, then `apply nonneg_of_eventually`."
  rw [le_iff_nonneg, sub_eq_add_neg, ofSeq_neg, ofSeq_add]
  apply nonneg_of_eventually
  use N
  intro n hn
  Hint "`rw [MyRat.addSeq_apply, MyRat.negSeq_apply, ← MyRat.sub_eq_add_neg, ← MyRat.le_iff_nonneg]`."
  rw [MyRat.addSeq_apply, MyRat.negSeq_apply, ← MyRat.sub_eq_add_neg, ← MyRat.le_iff_nonneg]
  exact hN n hn

Conclusion "
Inequalities between terms give inequalities between reals.
"

TheoremTab "≤ℝ"

end MyReal
