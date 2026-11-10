import Game.Levels.Inequalities.L05_IntEqZero

World "Inequalities"
Level 6
Title "Zero from both sides in ℚ"

namespace MyRat

open MyInt (mk)

Introduction "
The same for `ℚ`.
"

/-- If $x \ge 0$ and $-x \ge 0$, then $x = 0$. -/
Statement eq_zero_of_nonneg_neg (x : ℚ) : nonneg x → nonneg (-x) → x = 0 := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  intro h1 h2
  rw [neg_frac, nonneg_frac hb] at h2
  rw [nonneg_frac hb] at h1
  Hint "Get `a = 0` from the last level: `have ha : a = 0 := MyInt.eq_zero_of_nonneg_neg a {h1} {h2}`."
  have ha : a = 0 := MyInt.eq_zero_of_nonneg_neg a h1 h2
  Hint "Rewrite with `{ha}`, write `0` as `frac 0 1`, cross-multiply, and use `MyInt.zero_mul` twice."
  rw [ha, zero_def, frac_eq hb MyNat.one_ne_zero, MyInt.zero_mul, MyInt.zero_mul]

Conclusion "
Next we use this to compare two numbers.
"

TheoremTab "ℚ"

end MyRat
