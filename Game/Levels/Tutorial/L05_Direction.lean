import Game.Levels.Tutorial.L04_Errors

World "Tutorial"
Level 5
Title "Which way to rewrite"

Introduction "
`rw [h]` with `h : a = b` replaces `a` by `b`. It only goes left to right.

* To replace `b` by `a`, write `rw [← h]`. Type `←` as `\\l`.
* To rewrite a hypothesis `h₂` instead of the goal, write `rw [h] at h₂`.

A common error is:

```
did not find instance of the pattern in the target expression
```

It means: the left side of your equation is not where you rewrite.
Change the direction, or the place.
"

/-- If $a = b$ and $P(b)$, then $P(a)$. -/
Statement (α : Type) (P : α → Prop) (a b : α) (h : a = b) (hb : P b) : P a := by
  Hint "The goal mentions `{a}`. `{h}` turns `{a}` into `{b}`. Then `{hb}` fits."
  Branch
    rw [← h] at hb
    Hint "`{hb}` now says `P {a}`. That is the goal."
    exact hb
  rw [h]
  Hint "The goal is now `P {b}`. Which hypothesis is that?"
  exact hb

Conclusion "
Both ways work: change the goal with `rw [h]`, or change `hb` with `rw [← h] at hb`.
"
