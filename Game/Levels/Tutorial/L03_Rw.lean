import Game.Levels.Tutorial.L02_Rfl

World "Tutorial"
Level 3
Title "Rewriting"

Introduction "
If you know `h : a = b`, you may replace `a` by `b`.

The tactic `rw [h]` does this in the goal.
Note the square brackets.

After rewriting, `rw` tries `rfl` by itself.
"

/-- If $a = b$, then $f(a) = f(b)$. -/
Statement (α : Type) (a b : α) (f : α → α) (h : a = b) : f a = f b := by
  Hint "`{h}` says `{a} = {b}`. Use `rw [{h}]` to replace `{a}` by `{b}` in the goal."
  Hint (hidden := true) "Type `rw [{h}]`. Without brackets, `rw {h}` is an error."
  rw [h]

Conclusion "
After `rw [h]` the goal was `f b = f b`. Then `rw` closed it with `rfl`.
"

NewTactic rw
