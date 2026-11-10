import Game.Levels.RealOrder.L05_AddLeAddRight

World "RealOrder"
Level 6
Title "Antisymmetry"

namespace MyReal

open MyNat (succ)

Introduction "
If `x ≤ y` and `y ≤ x`, then `x = y`.

Unfold everything: `x ≤ y` says the terms of `t - s` are in the end `≥ -1/(k+1)`,
and `y ≤ x` says the same for `s - t`. Together: `s` and `t` are close.
"

/-- If $x \le y$ and $y \le x$, then $x = y$. -/
Statement le_antisymm (x y : ℝ) : x ≤ y → y ≤ x → x = y := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  obtain ⟨t, ht, rfl⟩ := exists_ofSeq y
  intro h1 h2
  Hint "Unfold both hypotheses:
  `rw [le_iff_nonneg, sub_eq_add_neg, ofSeq_neg, ofSeq_add, nonneg_ofSeq] at {h1} {h2}`."
  rw [le_iff_nonneg, sub_eq_add_neg, ofSeq_neg, ofSeq_add, nonneg_ofSeq] at h1 h2
  rw [ofSeq_eq]
  intro k
  obtain ⟨N1, a⟩ := h1 k
  obtain ⟨N2, b⟩ := h2 k
  use N1 + N2
  intro n hn
  have hn1 : N1 ≤ n := MyNat.le_trans N1 (N1 + N2) n (MyNat.le_add_right N1 N2) hn
  rw [MyNat.add_comm] at hn
  have hn2 : N2 ≤ n := MyNat.le_trans N2 (N2 + N1) n (MyNat.le_add_right N2 N1) hn
  have a1 := a n hn1
  have b1 := b n hn2
  rw [MyRat.addSeq_apply, MyRat.negSeq_apply] at a1 b1
  Hint "Turn `{a1}` around with `MyRat.neg_le_neg`: `have a2 := MyRat.neg_le_neg _ _ {a1}`.
  The same for `{b1}`."
  have a2 := MyRat.neg_le_neg _ _ a1
  have b2 := MyRat.neg_le_neg _ _ b1
  Hint "Clean up: `rw [MyRat.neg_neg, ← MyRat.sub_eq_add_neg, MyRat.neg_sub] at {a2} {b2}`."
  rw [MyRat.neg_neg, ← MyRat.sub_eq_add_neg, MyRat.neg_sub] at a2 b2
  constructor
  · exact a2
  · exact b2

Conclusion "
`≤` on `ℝ` is a partial order: reflexive, transitive, antisymmetric.
"

TheoremTab "≤ℝ"

end MyReal
