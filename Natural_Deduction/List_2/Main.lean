variable (p q r s : Prop)

theorem ex_1_a : (p ∧ q) → (p ∨ q) := by
  intro h1
  apply Or.inl
  apply And.left
  exact h1

theorem ex_1_b (p1 : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := by
  apply And.intro
  apply And.intro
  apply And.left p1
  apply And.left
  apply And.right p1
  apply And.right
  apply And.right p1

theorem ex_1_c (p1 : p ∨ (q ∧ r)) : (p ∨ q) ∧ (p ∨ r) := by
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

theorem ex_1_d (p1 : p ∧ (q ∨ r)) : (p ∧ q) ∨ (p ∧ r) := by
  have h1 : q ∨ r := And.right p1
  apply Or.elim h1
  intro h2
  apply Or.inl
  apply And.intro
  apply And.left p1
  exact h2
  intro h3
  apply Or.inr
  apply And.intro
  apply And.left p1
  exact h3

theorem ex_1_e (p1 : ¬(p ∨ q)) : ¬p ∨ ¬q := by
  apply Or.inl
  intro h1
  have h2 : p ∨ q := Or.inl h1
  apply p1 h2

theorem ex_1_f (p1 : ¬p ∧ ¬q) : ¬(p ∨ q) := by
  intro h1
  apply And.left p1
  apply Or.elim h1
  intro h2
  exact h2
  intro h3
  apply False.elim
  apply And.right p1
  apply h3

theorem ex_1_g (p1 : ¬(p ∧ q)) : ¬p ∨ ¬q := by
  have h1 : p ∨ ¬p := Classical.em p
  apply Or.elim h1
  have h2 : q ∨ ¬q := Classical.em q
  apply Or.elim h2
  intro h4
  intro h3
  apply False.elim
  apply p1
  apply And.intro
  exact h3
  exact h4
  intro h6
  intro h5
  apply Or.inr h6
  intro h7
  apply Or.inl h7

theorem ex_1_h : (p → q) → (¬p ∨ q) := by
  intro h1
  have h2 : p ∨ ¬p := Classical.em p
  apply Or.elim h2
  intro h3
  have h4 : q := (h1 h3)
  apply Or.inr h4
  intro h5
  apply Or.inl h5
