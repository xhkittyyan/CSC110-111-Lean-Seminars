import data.real.basic

/- 
Tactics you may consider 
-intro
-rw
-apply
-exact
-/

#check le_antisymm

-- BEGIN
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : ¬ x = y :=
begin
  intro h,
    /- In Lean, ¬ P is defined as an implication P → false.
       In this context, ¬ x = y means 'x = y → false'. intro h 
       simply introduces the hypothesis x = y and tells Lean to 
       find a contradiction. -/
  apply h₁,
    /- '¬ y ≤ x' is equivalent to y ≤ x → false by the definition 
       of negation. 'apply h₁' reverses this implication by matching 
       the goal with false and leaving y ≤ x as a new goal. -/
  rw h,
    /- Replace x with y so that the goal becomes ⊢ y ≤ y. Lean 
       knows this is true by le_refl: a ≤ a. -/
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  intro h',  
    /- In Lean, ¬ P is defined as an implication P → false.
       In this context, ¬ y ≤ x means 'y ≤ x → false'. intro h' 
       simply introduces the hypothesis y ≤ x and tells Lean to 
       find a contradiction. -/
  apply h.right,
    /- x ≠ y is eqivelant to ¬ x = y, meaning 'x = y → false' 
       by the definition of negation. 'apply h.right (x ≠ y)' reverses 
       this implication by matching the goal with false and leaving 
       x = y as a new goal. -/
  exact le_antisymm h.left h',
    /- le_antisymm refers to a ≤ b → b ≤ a → a = b; 'h.left' refers
       to x ≤ y; and h' is y ≤ x. exact le_antisymm h.left h' therefore
       solve the goal x = y. -/
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
λ h', h.right (le_antisymm h.left h')

-- END