import Game.Levels.Inequalities.L10_IntNonnegMul

World "Inequalities"
Level 11
Title "Products in ℚ"

namespace MyRat

Introduction "
Multiplication of fractions: `frac_mul_frac hb hd : frac a b * frac c d = frac (a * c) (b * d)`.
"

/-- If $x \ge 0$ and $y \ge 0$, then $xy \ge 0$. -/
Statement nonneg_mul (x y : ℚ) : nonneg x → nonneg y → nonneg (x * y) := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  obtain ⟨c, d, hd, rfl⟩ := exists_frac y
  intro hx hy
  rw [nonneg_frac hb] at hx
  rw [nonneg_frac hd] at hy
  Hint "Multiply with `frac_mul_frac`, then use `nonneg_frac`."
  Branch
    rw [frac_mul_frac hb hd]
    Hint "Now unfold `nonneg` with `nonneg_frac (MyNat.mul_ne_zero b d {hb} {hd})`."
  rw [frac_mul_frac hb hd, nonneg_frac (MyNat.mul_ne_zero b d hb hd)]
  exact MyInt.nonneg_mul a c hx hy

Conclusion "
You proved the basic rules of inequalities. Next: limits.
"

NewTheorem MyRat.frac_mul_frac
TheoremTab "ℚ"

end MyRat
