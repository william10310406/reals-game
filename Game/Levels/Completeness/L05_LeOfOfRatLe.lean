import Game.Levels.Completeness.L04_ExistsRatNear

World "Completeness"
Level 5
Title "Back to ℚ"

namespace MyReal

open MyNat (succ)

Introduction "
To show that the chosen rationals form a Cauchy sequence, we must bring inequalities from `ℝ`
back to `ℚ`. If `ofRat a ≤ ofRat b`, then `a ≤ b + 1/(k+1)` for every `k`.
"

/-- If $a \le b$ in $\mathbb{R}$, then $a \le b + \frac{1}{k+1}$ in $\mathbb{Q}$ for every $k$. -/
Statement le_of_ofRat_le (a b : ℚ) : ofRat a ≤ ofRat b → ∀ k, a ≤ b + MyRat.frac 1 (succ k) := by
  intro h k
  Hint "Unfold `{h}`: `rw [le_iff_nonneg, sub_eq_add_neg, ofRat_def, ofRat_def, ofSeq_neg, ofSeq_add,
  nonneg_ofSeq] at {h}`."
  rw [le_iff_nonneg, sub_eq_add_neg, ofRat_def, ofRat_def, ofSeq_neg, ofSeq_add, nonneg_ofSeq] at h
  obtain ⟨N, hN⟩ := h k
  Hint "Any term will do: `have a1 := hN N (MyNat.le_refl N)`."
  have a1 := hN N (MyNat.le_refl N)
  rw [MyRat.addSeq_apply, MyRat.const_apply, MyRat.negSeq_apply, MyRat.const_apply] at a1
  Hint "Add `a + frac 1 (succ k)` on both sides:
  `have a2 := MyRat.add_le_add_right _ _ (a + MyRat.frac 1 (succ k)) {a1}`."
  have a2 := MyRat.add_le_add_right _ _ (a + MyRat.frac 1 (succ k)) a1
  Hint "Simplify both sides with two `have … := by` steps (`ac_rfl`, `MyRat.add_neg`, `MyRat.add_zero`)."
  have e1 : -MyRat.frac 1 (succ k) + (a + MyRat.frac 1 (succ k)) = a := by
    have e : -MyRat.frac 1 (succ k) + (a + MyRat.frac 1 (succ k))
        = a + (MyRat.frac 1 (succ k) + -MyRat.frac 1 (succ k)) := by ac_rfl
    rw [e, MyRat.add_neg, MyRat.add_zero]
  have e2 : b + -a + (a + MyRat.frac 1 (succ k)) = b + MyRat.frac 1 (succ k) := by
    have e : b + -a + (a + MyRat.frac 1 (succ k)) = b + MyRat.frac 1 (succ k) + (a + -a) := by ac_rfl
    rw [e, MyRat.add_neg, MyRat.add_zero]
  rw [e1, e2] at a2
  exact a2

Conclusion "
`le_of_ofRat_le` brings inequalities back to `ℚ`, at the price of a small `1/(k+1)`.
"

TheoremTab "limℝ"

end MyReal
