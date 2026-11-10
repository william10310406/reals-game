import Game.Levels.RealOrder.L23_NonnegMul

World "RealOrder"
Level 24
Title "Triangle inequality in ℝ"

namespace MyReal

Introduction "
Last level of this world: `abs (x + y) ≤ abs x + abs y` for reals.
"

/-- $|x + y| \le |x| + |y|$ for reals. -/
Statement abs_add (x y : ℝ) : abs (x + y) ≤ abs x + abs y := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  obtain ⟨t, ht, rfl⟩ := exists_ofSeq y
  Hint "Compute: `ofSeq_add`, `ofSeq_abs` three times, `ofSeq_add`.
  Then `apply le_of_eventually`."
  rw [ofSeq_add, ofSeq_abs, ofSeq_abs, ofSeq_abs, ofSeq_add]
  apply le_of_eventually
  use 0
  intro n hn
  rw [MyRat.absSeq_apply, MyRat.addSeq_apply, MyRat.addSeq_apply, MyRat.absSeq_apply,
    MyRat.absSeq_apply]
  exact MyRat.abs_add (s n) (t n)

Conclusion "
`ℝ` has a total order that fits with `+` and `*`, and an absolute value with the
triangle inequality.
"

TheoremTab "abs"

end MyReal
