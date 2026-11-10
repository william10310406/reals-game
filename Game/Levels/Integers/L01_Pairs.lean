import Game.MyInt.Basic

World "Integers"
Level 1
Title "Pairs"

namespace MyInt

Introduction "
Natural numbers cannot go below zero. So we build new numbers.

An integer is a pair of naturals `mk a b`, read as `a - b`.
Different pairs can be the same integer: `mk 3 5` and `mk 0 2` are both `-2`.

The rule is `mk_eq : mk a b = mk c d ↔ a + d = c + b`.
It only uses `+` on `ℕ`, so we never need subtraction of naturals.

Theorems about `ℕ` keep their names with `MyNat.` in front, like `MyNat.add_comm`.
"

/-- $a - b = (a + 1) - (b + 1)$. -/
Statement (a b : ℕ) : mk a b = mk (a + 1) (b + 1) := by
  Hint "Turn the equality of integers into an equality of naturals: `rw [mk_eq]`."
  Branch
    rw [MyNat.add_comm a 1]
    Hint "Rewriting inside `mk` is fine, but first turn the equation of integers into one of naturals: `rw [mk_eq]`."
  rw [mk_eq]
  Hint "Now it is about `ℕ`. Try `rw [MyNat.add_assoc]`, then swap `1 + b` with `MyNat.add_comm`."
  rw [MyNat.add_assoc, MyNat.add_comm 1 b]

Conclusion "
Every question about integers becomes a question about naturals.
"

NewTheorem MyInt.mk_eq
NewDefinition MyInt MyInt.mk
TheoremTab "ℤ"

end MyInt
