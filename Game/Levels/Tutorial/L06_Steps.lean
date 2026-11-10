import Game.Levels.Tutorial.L05_Direction

World "Tutorial"
Level 6
Title "Several steps"

Introduction "
Most proofs need several steps. Write one tactic per line.

Two errors you will meet:

* `unsolved goals`: you stopped too early. There is still a goal.
* `no goals to be proved`: you wrote a line after the proof was done. Delete it.

`rw [h₁, h₂]` does two rewrites in one line.
"

/-- If $a = b$ and $b = c$, then $a = c$. -/
Statement (α : Type) (a b c : α) (h₁ : a = b) (h₂ : b = c) : a = c := by
  Hint "Rewrite `{a}` with `{h₁}` first."
  rw [h₁]
  Hint "Now the goal is `{b} = {c}`. Use `{h₂}`."
  rw [h₂]

Conclusion "
You finished the Tutorial. Next: logic.
"
