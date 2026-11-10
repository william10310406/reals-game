import Game.Levels.Inequalities.L04_NegLeNeg

World "Inequalities"
Level 5
Title "Zero from both sides in ℤ"

namespace MyInt

Introduction "
If `x ≥ 0` and `-x ≥ 0`, then `x = 0`. First in `ℤ`.

Your old friend `MyNat.eq_zero_of_add_eq_zero` will help.
"

/-- If $0 \le x$ and $0 \le -x$, then $x = 0$. -/
Statement eq_zero_of_nonneg_neg (x : ℤ) : 0 ≤ x → 0 ≤ -x → x = 0 := by
  intro h1 h2
  Branch
    rw [nonneg_iff] at h1
    Hint "Do `{h2}` too: `rw [nonneg_iff] at h1 h2`."
  rw [nonneg_iff] at h1 h2
  obtain ⟨c, rfl⟩ := h1
  obtain ⟨e, he⟩ := h2
  Hint "Simplify `{he}`: `rw [neg_mk, mk_eq, MyNat.zero_add] at {he}`."
  rw [neg_mk, mk_eq, MyNat.zero_add] at he
  Hint "Now the goal: `rw [zero_def, mk_eq, MyNat.add_zero, MyNat.zero_add]`."
  rw [zero_def, mk_eq, MyNat.add_zero, MyNat.zero_add]
  Hint "`{he} : 0 = e + c`. Use `apply MyNat.eq_zero_of_add_eq_zero e c`, then `rw [← {he}]`."
  apply MyNat.eq_zero_of_add_eq_zero e c
  rw [← he]

Conclusion "
An integer that is `≥ 0` and `≤ 0` is `0`.
"

TheoremTab "ℤ"

end MyInt
