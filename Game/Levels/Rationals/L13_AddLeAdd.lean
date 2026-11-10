import Game.Levels.Rationals.L12_LeTrans

World "Rationals"
Level 13
Title "Adding inequalities"

namespace MyRat

Introduction "
Boss level. Add two inequalities.
"

/-- If $a \le b$ and $c \le d$, then $a + c \le b + d$. -/
Statement add_le_add (a b c d : ℚ) : a ≤ b → c ≤ d → a + c ≤ b + d := by
  intro h1 h2
  Branch
    obtain ⟨p, q, hq, rfl⟩ := exists_frac a
    Hint "No fractions needed here: use `le_iff_nonneg`, the laws of `+` and `nonneg_add`."
  rw [le_iff_nonneg] at h1 h2 ⊢
  Hint "Show `b + d - (a + c) = b - a + (d - c)` first, with `have`.
  Inside: `sub_eq_add_neg` three times, `neg_add`, then `ac_rfl`."
  have h : b + d - (a + c) = b - a + (d - c) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add]
    ac_rfl
  rw [h]
  exact nonneg_add (b - a) (d - c) h1 h2

Conclusion "
You built `ℚ`: fractions, sums, negatives and order. Next: the reals.
"

TheoremTab "ℚ"

end MyRat
