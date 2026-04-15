import Mathlib.Tactic.WLOG

example (P Q : Prop) (h : P ∨ Q) : True := by
  wlog hP : P
  · trivial
  · trivial
