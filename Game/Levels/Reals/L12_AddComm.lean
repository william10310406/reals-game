import Game.MyReal.Add

World "Reals"
Level 12
Title "Adding reals"

namespace MyReal

Introduction "
Every real is `ofSeq s hs` for a Cauchy sequence `s` (theorem `exists_ofSeq`).

* `ofSeq_add : ofSeq s hs + ofSeq t ht = ofSeq (addSeq s t) _`
* `ofSeq_eq : ofSeq s hs = ofSeq t ht ↔ Close s t`

Show that addition of reals is commutative.
"

/-- $x + y = y + x$ for real numbers. -/
Statement add_comm (x y : ℝ) : x + y = y + x := by
  Hint "Write both reals as sequences: `obtain ⟨s, hs, rfl⟩ := exists_ofSeq x`."
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  obtain ⟨t, ht, rfl⟩ := exists_ofSeq y
  Hint "Add with `ofSeq_add` (twice), then compare with `ofSeq_eq`."
  rw [ofSeq_add, ofSeq_add, ofSeq_eq]
  intro k
  use 0
  intro n hn
  Hint "Compute the terms with `MyRat.addSeq_apply`, swap with `MyRat.add_comm (s n)`,
  then `MyRat.sub_eq_add_neg` and `MyRat.add_neg`."
  rw [MyRat.addSeq_apply, MyRat.addSeq_apply, MyRat.add_comm (s n)]
  rw [MyRat.sub_eq_add_neg, MyRat.add_neg]
  constructor
  exact MyRat.eps_nonneg k
  exact MyRat.eps_nonneg k

Conclusion "
You built the real numbers from nothing: logic, then `ℕ`, `ℤ`, `ℚ`, and now `ℝ`.
"

NewTheorem MyReal.exists_ofSeq MyReal.ofSeq_add MyReal.ofSeq_eq
NewDefinition MyReal MyReal.ofSeq
TheoremTab "ℝ"

end MyReal
