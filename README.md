This implements a Lean 4 tactic that proves set-theoretical tautologies. 

It should be able to prove any tautology involving hypotheses and goals of the form
X ⊆ Y or X = Y, where X, Y are expressions built using ∪, ∩, \, and ᶜ from
finitely many variables of type Set α. It also unfolds expressions of the form
Disjoint A B and symmDiff A B.

