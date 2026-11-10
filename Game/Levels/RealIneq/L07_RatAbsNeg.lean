import Game.Levels.RealIneq.L06_OfRatLe

World "RealIneq"
Level 7
Title "|−a| = |a| in ℚ"

namespace MyRat

Introduction "
`abs (-a) = abs a`. Split by the sign of `a`, then by the sign of `-a`.
"

/-- $|-a| = |a|$ for rationals. -/
Statement abs_neg (a : ℚ) : abs (-a) = abs a := by
  by_cases h : nonneg a
  · by_cases h2 : nonneg (-a)
    · Hint "Both signs: then `a = 0`. `have e := eq_zero_of_nonneg_neg a {h} {h2}`."
      have e := eq_zero_of_nonneg_neg a h h2
      rw [e, neg_zero]
    · rw [abs_of_nonneg h, abs_of_not_nonneg h2, neg_neg]
  · rw [abs_of_not_nonneg h]
    Hint "Now `-a ≥ 0`: `obtain h2 | h2 := nonneg_or_nonneg_neg a`."
    obtain h2 | h2 := nonneg_or_nonneg_neg a
    · exfalso
      exact h h2
    · rw [abs_of_nonneg h2]

Conclusion "
`abs` does not see the sign.
"

TheoremTab "abs"

end MyRat
