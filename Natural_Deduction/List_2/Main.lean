variable (p q r s : Prop)

theorem ex1 : (p ∧ q) → (p ∨ q) := by
  intro h1
  apply Or.inl
  apply And.left
  exact h1

theorem ex2 (h1 : ¬(p ∨ q)) : (¬p ∨ ¬q) := by
  apply Or.inl
  intro h2
  have h3 : p ∨ q := Or.inl h2
  apply h1
  exact h3
