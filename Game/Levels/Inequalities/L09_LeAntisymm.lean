import Game.Levels.Inequalities.L08_EqOfSub

World "Inequalities"
Level 9
Title "Antisymmetry"

namespace MyRat

Introduction "
If `x ≤ y` and `y ≤ x`, then `x = y`. This is how you prove equalities with inequalities.
"

/-- If $x \le y$ and $y \le x$, then $x = y$. -/
Statement le_antisymm (x y : ℚ) : x ≤ y → y ≤ x → x = y := by
  intro h1 h2
  rw [le_iff_nonneg] at h1 h2
  Hint "Write `x - y` in `{h2}` as `-(y - x)`: `rw [← neg_sub x y] at {h2}`."
  Branch
    rw [← neg_sub y x] at h1
    Hint "Turn `{h2}` around instead: `rw [← neg_sub x y] at {h2}`. Then both are about `y - x`."
  rw [← neg_sub x y] at h2
  Hint "Now `have h := eq_zero_of_nonneg_neg (y - x) {h1} {h2}`."
  have h := eq_zero_of_nonneg_neg (y - x) h1 h2
  have e := eq_of_sub_eq_zero x y h
  rw [e]

Conclusion "
`≤` on `ℚ` is a partial order: reflexive, transitive and antisymmetric.
"

TheoremTab "ℚ"

end MyRat
