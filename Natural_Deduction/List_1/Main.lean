variable (p q r s : Prop)

theorem ex1 (h1:q) : (p → q) ∨ ¬q  := by
  apply Or.inl
  intro h2
  exact h1
