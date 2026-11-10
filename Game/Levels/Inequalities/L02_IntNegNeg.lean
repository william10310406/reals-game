import Game.Levels.Inequalities.L01_AddLeAddRight

World "Inequalities"
Level 2
Title "Minus minus in ℤ"

namespace MyInt

Introduction "
Two minus signs cancel. First in `ℤ`.
"

/-- $-(-x) = x$ for integers. -/
Statement neg_neg (x : ℤ) : -(-x) = x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  Hint "Use `neg_mk` twice."
  Branch
    rw [neg_mk]
    Hint "One more `neg_mk` for the outer minus."
  rw [neg_mk, neg_mk]

Conclusion "
Swapping a pair twice gives the pair back.
"

TheoremTab "ℤ"

end MyInt
