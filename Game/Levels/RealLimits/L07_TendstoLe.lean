import Game.Levels.RealLimits.L06_LeOfForallEps

World "RealLimits"
Level 7
Title "Two limits, one inequality"

namespace MyReal

open MyNat (succ)

Introduction "
If `a → L` and `a → M`, then `L ≤ M`. Next level gives `M ≤ L` for free, so `L = M`.

Plan: `apply le_of_forall_eps`. For `k`, take `n = N1 + N2`. Then
`L - M = (L - a n) + (a n - M) ≤ eps k`.
"

/-- If $a_n \to L$ and $a_n \to M$, then $L \le M$. -/
Statement tendsto_le (a : ℕ → ℝ) (L M : ℝ) : Tendsto a L → Tendsto a M → L ≤ M := by
  intro h1 h2
  apply le_of_forall_eps
  intro k
  obtain ⟨N1, a1⟩ := h1 (succ k + k)
  obtain ⟨N2, a2⟩ := h2 (succ k + k)
  Hint "Use the index `N1 + N2` in both:
  `have b1 := {a1} (N1 + N2) (MyNat.le_add_right N1 N2)`."
  have b1 := a1 (N1 + N2) (MyNat.le_add_right N1 N2)
  Hint "For `{a2}` you need `N2 ≤ N1 + N2`. `have hn2 : N2 ≤ N1 + N2 := by …`
  (`rw [MyNat.add_comm]`, then `MyNat.le_add_right`)."
  have hn2 : N2 ≤ N1 + N2 := by
    rw [MyNat.add_comm]
    exact MyNat.le_add_right N2 N1
  have b2 := a2 (N1 + N2) hn2
  Hint "Remove the `abs`: `obtain ⟨c1, c2⟩ := abs_bounds (a (N1 + N2) - L)` and
  `obtain ⟨d1, d2⟩ := abs_bounds (a (N1 + N2) - M)`."
  obtain ⟨c1, c2⟩ := abs_bounds (a (N1 + N2) - L)
  obtain ⟨d1, d2⟩ := abs_bounds (a (N1 + N2) - M)
  have e1 := le_trans _ _ _ c2 b1
  have e2 := le_trans _ _ _ d1 b2
  rw [neg_sub] at e1
  Hint "Add `{e1}` and `{e2}`, then simplify with `sub_add_sub` and `eps_half`."
  have e3 := add_le_add _ _ _ _ e1 e2
  rw [sub_add_sub, eps_half] at e3
  Hint "Now `L - M ≤ eps k`. Add `M` on both sides with `add_le_add_right` and simplify."
  have e4 := add_le_add_right _ _ M e3
  rw [sub_eq_add_neg, add_assoc, add_comm (-M), add_neg, add_zero, add_comm] at e4
  exact e4

Conclusion "
Half of the uniqueness of limits.
"

TheoremTab "limℝ"

end MyReal
