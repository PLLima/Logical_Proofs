/-
  Compilation of Natural Deduction for Predicative Logic
  for the Logic for Computer Science Course
-/

variable (U : Prop)
variable (a b : U)
variable (P Q : U → Prop)
variable (R : U → U → Prop)


theorem ex5_a (p1: ∀x, P x → Q x) (p2: P a) : ∃x, Q x := by

  have h1: P a → Q a := p1 a
  have h2: Q a := h1 p2

  apply Exists.intro
  exact h2


theorem ex5_b (p1: ∃x, P x) : ¬∀x, ¬(P x) := by

  intro h1
  apply Exists.elim p1
  intro x0
  intro h2
  have h3: ¬(P x0) := h1 x0
  apply h3 h2


theorem ex5_c (p1: ∃x, P x ∧ Q x) (p2: ∀x, Q x → ¬(R a x)) : ∃x, P x ∧ ¬(R a x) := by

  apply Exists.elim p1
  intro x0
  intro h1
  exists x0
  apply And.intro

  apply And.left h1

  have h2: Q x0 → ¬(R a x0) := p2 x0
  have h3: Q x0 := And.right h1

  apply h2 h3

theorem ex5_d (p1: P b) : ∀x, x = b → P x := by

  intro x0
  intro h1
  apply Eq.subst h1 p1
