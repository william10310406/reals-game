import Game.Levels.RealIneq.L07_RatAbsNeg

World "RealIneq"
Level 8
Title "|−x| = |x| in ℝ"

namespace MyReal

Introduction "
Now for reals, term by term.
"

/-- $|-x| = |x|$ for reals. -/
Statement abs_neg (x : ℝ) : abs (-x) = abs x := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  Hint "`rw [ofSeq_neg, ofSeq_abs, ofSeq_abs, ofSeq_eq]`, then `apply MyRat.close_of_eq`."
  rw [ofSeq_neg, ofSeq_abs, ofSeq_abs, ofSeq_eq]
  apply MyRat.close_of_eq
  intro n
  rw [MyRat.absSeq_apply, MyRat.negSeq_apply, MyRat.absSeq_apply, MyRat.abs_neg]

Conclusion "
`abs_neg` is in your inventory.
"

TheoremTab "abs"

end MyReal
