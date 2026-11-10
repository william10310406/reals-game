import Game.Levels.RealArith.L16_MulOne

World "RealArith"
Level 17
Title "Distributivity in ℝ"

namespace MyReal

Introduction "
`x * (y + z) = x * y + x * z`. The hard work was `MyRat.mul_add`.
"

/-- $x(y + z) = xy + xz$ for reals. -/
Statement mul_add (x y z : ℝ) : x * (y + z) = x * y + x * z := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  obtain ⟨t, ht, rfl⟩ := exists_ofSeq y
  obtain ⟨u, hu, rfl⟩ := exists_ofSeq z
  Hint "Left side: `ofSeq_add`, then `ofSeq_mul`. Right side: `ofSeq_mul` twice, then `ofSeq_add`.
  Then `ofSeq_eq`."
  rw [ofSeq_add, ofSeq_mul, ofSeq_mul, ofSeq_mul, ofSeq_add, ofSeq_eq]
  apply MyRat.close_of_eq
  intro n
  Hint "Compute the terms (`MyRat.mulSeq_apply`, `MyRat.addSeq_apply`), then `MyRat.mul_add`."
  rw [MyRat.mulSeq_apply, MyRat.addSeq_apply, MyRat.addSeq_apply, MyRat.mulSeq_apply,
    MyRat.mulSeq_apply]
  exact MyRat.mul_add (s n) (t n) (u n)

Conclusion "
`ℝ` is a commutative ring: all the rules of `+`, `-`, `*`, `0`, `1` hold.
"

TheoremTab "ℝ"

end MyReal
