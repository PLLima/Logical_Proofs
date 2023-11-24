/-
  List 1 of Natural Deduction
  for the Logic for Computer Science Course
-/

variable (p q r s : Prop)

theorem ex_1_a (p1 : q) : (p → q) ∨ ¬q  := by
  apply Or.inl
  intro h1
  exact p1

theorem ex_1_b (p1 : p → q) (p2 : ¬q) : ¬p := by
  intro h1
  apply p2
  apply p1
  exact h1

theorem ex_1_c (p1 : p ∧ (q ∧ s)) : p ∧ s := by
  apply And.intro
  apply And.left p1
  apply And.right
  apply And.right p1

theorem ex_1_d (p1 : p ∧ q) : q ∧ p := by
  apply And.intro
  apply And.right p1
  apply And.left p1

theorem ex_1_e (p1 : p) : q → (p → p) := by
  intro h1
  intro h2
  exact p1

theorem ex_1_f (p1 : p → r ∧ s) (p2 : q → r ∧ s) (p3 : p ∨ q) : r := by
  apply And.left
  apply Or.elim p3
  apply p1
  apply p2

theorem ex_1_g (p1 : ¬p ∨ q) : (¬p ∨ ¬q) ∨ q := by
  apply Or.elim p1
  intro h1
  apply Or.inl
  apply Or.inl
  exact h1
  intro h2
  apply Or.inr
  exact h2
