import Game.Levels.RealOrder.L16_RatAbsNonneg

World "RealOrder"
Level 17
Title "a and -a are below |a|"

namespace MyRat

Introduction "
Both `a` and `-a` are `≤ abs a`.
"

/-- $a \le |a|$ and $-a \le |a|$ for rationals. -/
Statement abs_bounds (a : ℚ) : a ≤ abs a ∧ -a ≤ abs a := by
  by_cases h : nonneg a
  · rw [abs_of_nonneg h]
    constructor
    · exact le_refl a
    · Hint "`-a ≤ a`: unfold with `rw [le_iff_nonneg, sub_eq_add_neg, neg_neg]`, then `nonneg_add`."
      rw [le_iff_nonneg, sub_eq_add_neg, neg_neg]
      exact nonneg_add a a h h
  · rw [abs_of_not_nonneg h]
    obtain h2 | h2 := nonneg_or_nonneg_neg a
    · exfalso
      exact h h2
    · constructor
      · Hint "`a ≤ -a`: `rw [le_iff_nonneg, sub_eq_add_neg]`, then `nonneg_add`."
        rw [le_iff_nonneg, sub_eq_add_neg]
        exact nonneg_add (-a) (-a) h2 h2
      · exact le_refl (-a)

Conclusion "
Use it as `obtain ⟨h1, h2⟩ := abs_bounds a`.
"

TheoremTab "abs"

end MyRat
