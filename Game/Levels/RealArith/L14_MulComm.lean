import Game.Levels.RealArith.L13_NegSub

World "RealArith"
Level 14
Title "Multiplying reals"

namespace MyReal

Introduction "
Reals multiply term by term.

* `ofSeq_mul : ofSeq s hs * ofSeq t ht = ofSeq (MyRat.mulSeq s t) _`
* `MyRat.mulSeq_apply s t n : MyRat.mulSeq s t n = s n * t n`

(That the product of Cauchy sequences is Cauchy, and that the product does not depend on
the chosen sequences, is checked behind the scenes.)
"

/-- $xy = yx$ for reals. -/
Statement mul_comm (x y : ℝ) : x * y = y * x := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  obtain ⟨t, ht, rfl⟩ := exists_ofSeq y
  Hint "Same recipe: `rw [ofSeq_mul, ofSeq_mul, ofSeq_eq]`, `apply MyRat.close_of_eq`, `intro n`."
  rw [ofSeq_mul, ofSeq_mul, ofSeq_eq]
  apply MyRat.close_of_eq
  intro n
  Hint "`rw [MyRat.mulSeq_apply, MyRat.mulSeq_apply, MyRat.mul_comm]`."
  rw [MyRat.mulSeq_apply, MyRat.mulSeq_apply, MyRat.mul_comm]

Conclusion "
Multiplication of reals commutes.
"

NewTheorem MyReal.ofSeq_mul MyRat.mulSeq_apply
NewDefinition MyRat.mulSeq
TheoremTab "ℝ"

end MyReal
