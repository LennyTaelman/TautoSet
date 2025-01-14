This implements a Lean 4 tactic that proves set-theoretical tautologies. 

It should be able to prove any tautology involving hypotheses and goals of the form
X ⊆ Y or X = Y, where X, Y are expressions built from finitely many variables of type
Set α using intersections, unions, set-theoretic differences and complements.

This is now a mathlib pull request: https://github.com/leanprover-community/mathlib4/pull/20706
