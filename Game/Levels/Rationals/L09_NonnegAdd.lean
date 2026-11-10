import Game.Levels.Rationals.L08_AddAssoc

World "Rationals"
Level 9
Title "Positive part"

namespace MyRat

open MyInt (mk)

Introduction "
Order on `ℚ` starts with `nonneg x`, which means `x ≥ 0`.

For fractions: `nonneg_frac hb : nonneg (frac a b) ↔ 0 ≤ a`.
The denominator is a natural number, so only the numerator decides the sign.
"

/-- If $x \ge 0$ and $y \ge 0$, then $x + y \ge 0$. -/
Statement nonneg_add (x y : ℚ) : nonneg x → nonneg y → nonneg (x + y) := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  obtain ⟨c, d, hd, rfl⟩ := exists_frac y
  intro hx hy
  Hint "Add the fractions, then use `nonneg_frac` with the proof `MyNat.mul_ne_zero b d {hb} {hd}`."
  rw [frac_add_frac hb hd, nonneg_frac (MyNat.mul_ne_zero b d hb hd)]
  Hint "Use `nonneg_frac` at `{hx}` and `{hy}` too."
  rw [nonneg_frac hb] at hx
  rw [nonneg_frac hd] at hy
  Hint "Now it is about `ℤ`. Use `MyInt.nonneg_add` and `MyInt.nonneg_mul_mk`."
  exact MyInt.nonneg_add (a * mk d 0) (c * mk b 0) (MyInt.nonneg_mul_mk a d hx) (MyInt.nonneg_mul_mk c b hy)

Conclusion "
The order on `ℚ` reduces to the order on `ℤ`.
"

NewTheorem MyRat.nonneg_frac
NewDefinition MyRat.nonneg
TheoremTab "ℚ"

end MyRat
