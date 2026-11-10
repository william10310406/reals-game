import Game.Levels.RealOrder.L13_RatLeTotal

World "RealOrder"
Level 14
Title "Signs in ℝ"

namespace MyReal

open MyNat (succ)

Introduction "
Boss level. Every real `x` is `≥ 0`, or `-x` is.

The idea. Suppose `x = ofSeq s hs` is **not** `≥ 0`. Then for some `k`, the terms go below
`-1/(k+1)` again and again: for every `M` there is an `n ≥ M` with `s n ≤ -1/(k+1)`.
Now take `M` from the Cauchy property for this `k`: for `m, n ≥ M`, `s m - s n ≤ 1/(k+1)`.
Pick such an `n` with `s n ≤ -1/(k+1)`. Then `s m ≤ 0` for every `m ≥ M`. So `-x ≥ 0`.
"

/-- For reals, $x \ge 0$ or $-x \ge 0$. -/
Statement nonneg_or_nonneg_neg (x : ℝ) : nonneg x ∨ nonneg (-x) := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  Hint "`by_cases h : nonneg (ofSeq s hs)`."
  Branch
    right
    Hint "`-x ≥ 0` is not always true. Split into cases first: `by_cases h : nonneg (ofSeq s hs)`."
  by_cases h : nonneg (ofSeq s hs)
  · left
    exact h
  · right
    Hint "Unfold: `rw [nonneg_ofSeq] at {h}` and `rw [ofSeq_neg, nonneg_ofSeq]`."
    rw [nonneg_ofSeq] at h
    rw [ofSeq_neg, nonneg_ofSeq]
    Hint "Get the bad `k`: `obtain ⟨k, hk⟩ := MyLogic.not_forall _ _ {h}`."
    obtain ⟨k, hk⟩ := MyLogic.not_forall _ _ h
    Hint "Take `M` from the Cauchy property for this `k`: `obtain ⟨M, hM⟩ := hs k`."
    obtain ⟨M, hM⟩ := hs k
    intro j
    use M
    intro m hm
    rw [MyRat.negSeq_apply]
    Hint "Now find a bad `n ≥ M`. First `have hk2 := MyLogic.not_exists _ _ {hk} M`,
    then `obtain ⟨n, hn⟩ := MyLogic.not_forall _ _ hk2` and
    `obtain ⟨hMn, hlt⟩ := MyLogic.not_imp _ _ hn`."
    have hk2 := MyLogic.not_exists _ _ hk M
    obtain ⟨n, hn⟩ := MyLogic.not_forall _ _ hk2
    obtain ⟨hMn, hlt⟩ := MyLogic.not_imp _ _ hn
    Hint "Show `s n ≤ -frac 1 (succ k)` with `have h1 : … := by` and `MyRat.le_total`."
    have h1 : s n ≤ -MyRat.frac 1 (succ k) := by
      obtain h4 | h4 := MyRat.le_total (-MyRat.frac 1 (succ k)) (s n)
      · exfalso
        exact hlt h4
      · exact h4
    Hint "Add `hM m n {hm} {hMn}` and `{h1}`: `have h2 := MyRat.add_le_add _ _ _ _ (hM m n {hm} {hMn}) {h1}`."
    have h2 := MyRat.add_le_add _ _ _ _ (hM m n hm hMn) h1
    Hint "Simplify `{h2}` to `s m ≤ 0`: `MyRat.add_neg`, `MyRat.sub_eq_add_neg`, `MyRat.add_assoc`,
    `MyRat.add_comm (-s n)`, `MyRat.add_neg`, `MyRat.add_zero`."
    rw [MyRat.add_neg, MyRat.sub_eq_add_neg, MyRat.add_assoc, MyRat.add_comm (-s n), MyRat.add_neg,
      MyRat.add_zero] at h2
    Hint "Turn it around: `have h5 := MyRat.neg_le_neg _ _ {h2}` and `rw [MyRat.neg_zero] at h5`."
    have h5 := MyRat.neg_le_neg _ _ h2
    rw [MyRat.neg_zero] at h5
    Hint "Chain with `MyRat.le_trans` through `0`."
    exact MyRat.le_trans _ 0 _ (MyRat.neg_eps_le j) h5

Conclusion "
Every real has a sign. This used the Cauchy property and `by_cases`.
"

TheoremTab "≤ℝ"

end MyReal
