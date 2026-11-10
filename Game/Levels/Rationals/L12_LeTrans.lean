import Game.Levels.Rationals.L11_SubAddSub

World "Rationals"
Level 12
Title "Chains"

namespace MyRat

Introduction "
`z - x` is `(z - y) + (y - x)`. Both parts are `≥ 0`.
"

/-- If $x \le y$ and $y \le z$, then $x \le z$. -/
Statement le_trans (x y z : ℚ) : x ≤ y → y ≤ z → x ≤ z := by
  intro hxy hyz
  rw [le_iff_nonneg] at hxy hyz ⊢
  Hint "Split `z - x` at `y`: `rw [← sub_add_sub x y z]`."
  rw [← sub_add_sub x y z]
  Hint "Use `nonneg_add` with `{hyz}` and `{hxy}`."
  exact nonneg_add (z - y) (y - x) hyz hxy

Conclusion "
`≤` on `ℚ` is transitive.
"

TheoremTab "ℚ"

end MyRat
