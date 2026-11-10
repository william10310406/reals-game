import Game.Levels.RealLimits.L05_TendstoAdd

World "RealLimits"
Level 6
Title "Below every bound"

namespace MyReal

open MyNat (succ)

Introduction "
If `x ≤ y + eps k` for every `k`, then `x ≤ y`. A standard lemma: to show `x ≤ y`, it is
enough to show `x ≤ y + ε` for every `ε > 0`.

Write `x`, `y` as sequences and unfold everything. Use the hypothesis with half of `eps j`.
"

/-- If $x \le y + \frac{1}{k+1}$ for every $k$, then $x \le y$. -/
Statement le_of_forall_eps (x y : ℝ) : (∀ k, x ≤ y + eps k) → x ≤ y := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  obtain ⟨t, ht, rfl⟩ := exists_ofSeq y
  intro h
  rw [le_iff_nonneg, sub_eq_add_neg, ofSeq_neg, ofSeq_add, nonneg_ofSeq]
  intro j
  Hint "Use `{h}` with half of `eps j`: `have hj := {h} (succ j + j)`."
  have hj := h (succ j + j)
  Hint "Unfold `{hj}`: `rw [eps_def, ofRat_def, ofSeq_add, le_iff_nonneg, sub_eq_add_neg, ofSeq_neg,
  ofSeq_add, nonneg_ofSeq] at {hj}`."
  rw [eps_def, ofRat_def, ofSeq_add, le_iff_nonneg, sub_eq_add_neg, ofSeq_neg, ofSeq_add,
    nonneg_ofSeq] at hj
  Hint "Again half: `obtain ⟨N, hN⟩ := {hj} (succ j + j)`."
  obtain ⟨N, hN⟩ := hj (succ j + j)
  use N
  intro n hn
  have a := hN n hn
  rw [MyRat.addSeq_apply, MyRat.addSeq_apply, MyRat.const_apply, MyRat.negSeq_apply] at a
  rw [MyRat.addSeq_apply, MyRat.negSeq_apply]
  Hint "Add `-frac 1 (succ (succ j + j))` on both sides:
  `have b := MyRat.add_le_add_right _ _ (-MyRat.frac 1 (succ (succ j + j))) {a}`."
  have b := MyRat.add_le_add_right _ _ (-MyRat.frac 1 (succ (succ j + j))) a
  Hint "The right side of `{b}` is `t n + -s n`, regrouped. Show it with `have e : … := by`:
  first an `ac_rfl` step that puts `frac … + -frac …` together, then `MyRat.add_neg`, `MyRat.add_zero`."
  have e : t n + MyRat.frac 1 (succ (succ j + j)) + -s n + -MyRat.frac 1 (succ (succ j + j))
      = t n + -s n := by
    have e2 : t n + MyRat.frac 1 (succ (succ j + j)) + -s n + -MyRat.frac 1 (succ (succ j + j))
        = t n + -s n + (MyRat.frac 1 (succ (succ j + j)) + -MyRat.frac 1 (succ (succ j + j))) := by
      ac_rfl
    rw [e2, MyRat.add_neg, MyRat.add_zero]
  Hint "Now `rw [{e}, ← MyRat.neg_add, ← MyNat.add_succ, MyRat.half (succ j) (MyNat.succ_ne_zero j)] at {b}`."
  rw [e, ← MyRat.neg_add, ← MyNat.add_succ, MyRat.half (succ j) (MyNat.succ_ne_zero j)] at b
  exact b

Conclusion "
`le_of_forall_eps` turns `≤ y + ε for all ε` into `≤ y`.
"

TheoremTab "limℝ"

end MyReal
