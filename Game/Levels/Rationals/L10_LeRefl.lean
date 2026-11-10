import Game.Levels.Rationals.L09_NonnegAdd

World "Rationals"
Level 10
Title "Less or equal"

namespace MyRat

open MyInt (mk)

Introduction "
`x ≤ y` means `nonneg (y - x)` (theorem `le_iff_nonneg`),
and `x - y` means `x + -y` (theorem `sub_eq_add_neg`).
"

/-- $x \le x$ for rationals. -/
Statement le_refl (x : ℚ) : x ≤ x := by
  Hint "Unfold: `rw [le_iff_nonneg, sub_eq_add_neg]`."
  rw [le_iff_nonneg, sub_eq_add_neg]
  Hint "`add_neg`, then write `0` as a fraction with `zero_def`, then `nonneg_frac MyNat.one_ne_zero`."
  Branch
    rw [add_comm]
    Hint "Now `add_neg` does not fit: it simplifies `x + -x`, not `-x + x`."
  rw [add_neg, zero_def, nonneg_frac MyNat.one_ne_zero]
  Hint (hidden := true) "The goal is `0 ≤ 0` in `ℤ`: `exact MyInt.le_refl 0`."
  exact MyInt.le_refl 0

Conclusion "
`≤` on `ℚ` is reflexive.
"

NewTheorem MyRat.le_iff_nonneg MyRat.sub_eq_add_neg
TheoremTab "ℚ"

end MyRat
