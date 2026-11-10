import Game.Levels.RealLimits.L07_TendstoLe

World "RealLimits"
Level 8
Title "Limits are unique"

namespace MyReal

Introduction "
A sequence has at most one limit.
"

/-- If $a_n \to L$ and $a_n \to M$, then $L = M$. -/
Statement tendsto_unique (a : ℕ → ℝ) (L M : ℝ) : Tendsto a L → Tendsto a M → L = M := by
  intro h1 h2
  Hint "`apply le_antisymm`, then the last level twice."
  apply le_antisymm
  · exact tendsto_le a L M h1 h2
  · exact tendsto_le a M L h2 h1

Conclusion "
So we can say *the* limit.
"

TheoremTab "limℝ"

end MyReal
