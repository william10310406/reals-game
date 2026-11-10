import Game.Levels.RealOrder.L22_AbsOfNonneg

World "RealOrder"
Level 23
Title "Products of nonnegative reals"

namespace MyReal

Introduction "
`≤` and `*` fit together: if `x ≥ 0` and `y ≥ 0`, then `x * y ≥ 0`.

The terms of `x` may be a little negative, so multiplying the terms directly does not work.
But `x = abs x`, and the terms of `abs x` are `≥ 0`.
"

/-- If $x \ge 0$ and $y \ge 0$, then $xy \ge 0$. -/
Statement nonneg_mul (x y : ℝ) : nonneg x → nonneg y → nonneg (x * y) := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  obtain ⟨t, ht, rfl⟩ := exists_ofSeq y
  intro hx hy
  Hint "Replace the reals by their absolute values:
  `rw [← abs_of_nonneg (ofSeq s hs) {hx}, ← abs_of_nonneg (ofSeq t ht) {hy}]`."
  Branch
    rw [ofSeq_mul, nonneg_ofSeq]
    Hint "Now you would need bounds on the products of the terms. Easier: go back and replace
    `ofSeq s hs` by `abs (ofSeq s hs)` first."
  rw [← abs_of_nonneg (ofSeq s hs) hx, ← abs_of_nonneg (ofSeq t ht) hy]
  rw [ofSeq_abs, ofSeq_abs, ofSeq_mul]
  apply nonneg_of_eventually
  use 0
  intro n hn
  rw [MyRat.mulSeq_apply, MyRat.absSeq_apply, MyRat.absSeq_apply]
  Hint "This is `MyRat.nonneg_mul` with `MyRat.abs_nonneg`."
  exact MyRat.nonneg_mul _ _ (MyRat.abs_nonneg (s n)) (MyRat.abs_nonneg (t n))

Conclusion "
`≤` is compatible with `*`.
"

TheoremTab "≤ℝ"

end MyReal
