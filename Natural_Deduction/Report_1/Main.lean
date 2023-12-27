/-
  Report 1 of Natural Deduction
  for the Logic for Computer Science Course

  This includes theorems related to Propositional and
  Predicative Logic
-/

variable (p q r s : Prop)

theorem q_4_1 (p1 : p ∧ q → r) : p → (q → r) := by

  intro h1
  intro h2
  have  h3 : p ∧ q := And.intro h1 h2
  apply p1 h3

theorem q_4_2 (p1 : p ∨ False) (p2 : p → q) : s → q := by

  apply Or.elim p1

  intro h1
  intro h2
  apply p2 h1

  intro h3
  apply False.elim h3

theorem q_4_3 (p1 : p ∨ (q ∧ r)) : (p ∨ q) ∧ (p ∨ r) := by

  apply And.intro

  apply Or.elim p1

  intro h1
  apply Or.inl h1

  intro h2
  apply Or.inr
  apply And.left h2

  apply Or.elim p1

  intro h3
  apply Or.inl h3

  intro h4
  apply Or.inr
  apply And.right h4

theorem q_4_4 (p1 : ¬(p → q)) : p ∧ ¬q := by

  have h1 : p ∨ ¬p := Classical.em p
  apply Or.elim h1

  intro h2
  apply And.intro h2
  intro h3
  apply p1
  intro h4
  exact h3

  intro h5
  apply False.elim
  apply p1
  intro h6
  apply False.elim
  apply h5 h6

variable (U : Prop)
variable (a : U)
variable (P Q R : U → Prop)

theorem q_5_1 (p1 : R a) : ∀x, ∃y, P x → R y := by
  intro x0
  apply Exists.intro
  intro h1
  exact p1

theorem q_5_2 (p1 : ∀x, P x) : ¬∃x, ¬(P x) := by
  intro h1
  apply Exists.elim h1
  intro x0
  intro h2
  have h3 : P x0 := p1 x0
  apply h2 h3

theorem q_5_3 (p1 : ¬∃x, P x) : ∀x, ¬(P x) := by
  intro x0
  intro h1
  apply p1
  exists x0

theorem q_5_4 (p1 : ∀x, P x) (p2 : ∃z, Q z) : ∃w, Q w ∧ P w := by
  apply Exists.elim p2
  intro z0
  intro h1
  have h2 : P z0 := p1 z0
  have h3 : Q z0 ∧ P z0 := And.intro h1 h2
  exists z0
