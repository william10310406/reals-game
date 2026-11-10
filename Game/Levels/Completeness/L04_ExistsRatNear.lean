import Game.Levels.Completeness.L03_TendstoRatSeq

World "Completeness"
Level 4
Title "A rational nearby"

namespace MyReal

Introduction "
Next to every real there is a rational, as close as you want.
"

/-- For every real $x$ and every $k$ there is a rational $q$ with $|x - q| \le \frac{1}{k+1}$. -/
Statement exists_rat_near (x : ℝ) (k : ℕ) : ∃ q : ℚ, abs (x - ofRat q) ≤ eps k := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  Hint "Use the last level: `obtain ⟨N, hN⟩ := tendsto_ratSeq s hs k`."
  obtain ⟨N, hN⟩ := tendsto_ratSeq s hs k
  Hint "The term `s N` works: `use s N`."
  use s N
  have h := hN N (MyNat.le_refl N)
  Hint "`rw [ratSeq_apply, abs_sub_comm] at {h}`."
  rw [ratSeq_apply, abs_sub_comm] at h
  exact h

Conclusion "
Now we can pick a rational next to each `a n`.
"

TheoremTab "limℝ"

end MyReal
