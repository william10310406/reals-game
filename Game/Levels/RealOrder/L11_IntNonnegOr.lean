import Game.Levels.RealOrder.L10_NatLeTotal

World "RealOrder"
Level 11
Title "Signs in ℤ"

namespace MyInt

Introduction "
Every integer is `≥ 0`, or its negative is.
`mk a b` is `a - b`, and `-mk a b = mk b a`. Compare `a` and `b` with `MyNat.le_total`.
"

/-- For integers, $x \ge 0$ or $-x \ge 0$. -/
Statement nonneg_or_nonneg_neg (x : ℤ) : 0 ≤ x ∨ 0 ≤ -x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  Hint "`rw [neg_mk, nonneg_iff, nonneg_iff]`."
  rw [neg_mk, nonneg_iff, nonneg_iff]
  Hint "Compare `b` and `a`: `obtain h | h := MyNat.le_total b a`."
  Branch
    left
    Hint "You do not know yet which side is true. First compare:
    `obtain h | h := MyNat.le_total b a`."
  obtain h | h := MyNat.le_total b a
  · left
    rw [MyNat.le_iff_exists_add] at h
    obtain ⟨c, hc⟩ := h
    use c
    Hint "`rw [mk_eq, {hc}, MyNat.add_zero, MyNat.add_comm]`."
    rw [mk_eq, hc, MyNat.add_zero, MyNat.add_comm]
  · right
    rw [MyNat.le_iff_exists_add] at h
    obtain ⟨c, hc⟩ := h
    use c
    rw [mk_eq, hc, MyNat.add_zero, MyNat.add_comm]

Conclusion "
Every integer has a sign.
"

TheoremTab "ℤ"

end MyInt
