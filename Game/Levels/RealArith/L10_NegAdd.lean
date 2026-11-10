import Game.Levels.RealArith.L09_AddNeg

World "RealArith"
Level 10
Title "Negative of a sum"

namespace MyReal

Introduction "
Three negatives and two sums of reals. Rewrite until everything is one sequence on each side.
"

/-- $-(x + y) = -x + -y$ for reals. -/
Statement neg_add (x y : ℝ) : -(x + y) = -x + -y := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  obtain ⟨t, ht, rfl⟩ := exists_ofSeq y
  Hint "`rw [ofSeq_add, ofSeq_neg, ofSeq_neg, ofSeq_neg, ofSeq_add, ofSeq_eq]`."
  rw [ofSeq_add, ofSeq_neg, ofSeq_neg, ofSeq_neg, ofSeq_add, ofSeq_eq]
  apply MyRat.close_of_eq
  intro n
  Hint "Compute the terms (`MyRat.negSeq_apply`, `MyRat.addSeq_apply`), then use `MyRat.neg_add`."
  rw [MyRat.negSeq_apply, MyRat.addSeq_apply, MyRat.addSeq_apply, MyRat.negSeq_apply,
    MyRat.negSeq_apply]
  exact MyRat.neg_add (s n) (t n)

Conclusion "
`-` splits over `+`, in `ℝ` as in `ℚ`.
"

TheoremTab "ℝ"

end MyReal
