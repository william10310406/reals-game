import Game.Levels.RealArith.L08_ZeroAdd

World "RealArith"
Level 9
Title "Negatives"

namespace MyReal

Introduction "
The negative of a real negates the sequence term by term.

* `ofSeq_neg : -ofSeq s hs = ofSeq (MyRat.negSeq s) _`
* `MyRat.negSeq_apply s n : MyRat.negSeq s n = -s n`
"

/-- $x + (-x) = 0$ for reals. -/
Statement add_neg (x : ℝ) : x + -x = 0 := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  Hint "Compute `-x` with `ofSeq_neg`, add with `ofSeq_add`, and write `0` with `zero_def, ofRat_def`."
  Branch
    rw [zero_def, ofRat_def]
    Hint "Good. But `-ofSeq s hs` is not of the form `ofSeq …` yet, so `ofSeq_add` cannot see it.
    Use `rw [ofSeq_neg]` next."
  rw [ofSeq_neg, ofSeq_add, zero_def, ofRat_def, ofSeq_eq]
  apply MyRat.close_of_eq
  intro n
  Hint "Compute the terms, then `MyRat.add_neg`."
  rw [MyRat.addSeq_apply, MyRat.negSeq_apply, MyRat.const_apply, MyRat.add_neg]

Conclusion "
Every real has a negative.
"

NewTheorem MyReal.ofSeq_neg MyRat.negSeq_apply
NewDefinition MyRat.negSeq
TheoremTab "ℝ"

end MyReal
