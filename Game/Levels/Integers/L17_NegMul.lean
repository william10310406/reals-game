import Game.Levels.Integers.L16_NegAdd

World "Integers"
Level 17
Title "Minus times"

namespace MyInt

Introduction "
Show that `-x * y = -(x * y)`.
"

/-- $(-x) y = -(xy)$. -/
Statement neg_mul (x y : ℤ) : -x * y = -(x * y) := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  obtain ⟨c, d, rfl⟩ := exists_mk y
  Hint "Compute both sides: `neg_mk`, `mk_mul_mk` twice, `neg_mk`."
  rw [neg_mk, mk_mul_mk, mk_mul_mk, neg_mk]
  Hint "Finish with `mk_eq` and `ac_rfl`."
  rw [mk_eq]
  ac_rfl

Conclusion "
Signs move out of products.
"

TheoremTab "ℤ"

end MyInt
