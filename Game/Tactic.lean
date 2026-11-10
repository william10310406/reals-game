/-!
# Custom tactics

Small macros on top of Lean core tactics. They keep the game free of Mathlib.

* `use x` proves `∃ y, P y` by giving the witness `x`.
* `induction n with d hd` and `cases n with d` name the new variables,
  like in the Natural Number Game (NNG4, Apache 2.0). Our versions are written
  from scratch as macros over the core tactics.
-/

/-- `use x` turns the goal `∃ y, P y` into `P x`. -/
macro "use " x:term : tactic => `(tactic| refine ⟨$x, ?_⟩)

/-- `induction n with d hd` does induction on `n`. The new variable is `d`,
the induction hypothesis is `hd`. -/
syntax (name := inductionWith) "induction " term " with " ident ppSpace ident : tactic

set_option hygiene false in
macro_rules
  | `(tactic| induction $x:term with $d:ident $h:ident) =>
    `(tactic| induction $x:term with
      | zero => ?_
      | succ $d:ident $h:ident => ?_)

/-- `cases n with d` splits into the cases `0` and `succ d`. -/
syntax (name := casesWith) "cases " term " with " ident : tactic

set_option hygiene false in
macro_rules
  | `(tactic| cases $x:term with $d:ident) =>
    `(tactic| cases $x:term with
      | zero => ?_
      | succ $d:ident => ?_)
