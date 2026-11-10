import Game.Levels.Integers.L15_ZeroMul

World "Integers"
Level 16
Title "Minus a sum"

namespace MyInt

Introduction "
Show that `-(x + y) = -x + -y`.
"

/-- $-(x + y) = -x + (-y)$. -/
Statement neg_add (x y : ℤ) : -(x + y) = -x + -y := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  obtain ⟨c, d, rfl⟩ := exists_mk y
  Hint "Compute: `mk_add_mk`, then `neg_mk` three times, then `mk_add_mk`."
  rw [mk_add_mk, neg_mk, neg_mk, neg_mk, mk_add_mk]

Conclusion "
Negation spreads over sums.
"

TheoremTab "ℤ"

end MyInt
