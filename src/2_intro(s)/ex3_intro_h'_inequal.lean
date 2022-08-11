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
    In this context, ¬ x = y means 'x = y → false'. intro h' 
    simply introduces the assumption x = y and tells Lean to 
    find a contradiction. -/
  apply h₁,
    /- apply h₁ changes the goal to y ≤ x because ¬ y ≤ x means 
    y ≤ x → false" by the definition of negation. apply h₁ (¬ y ≤ x)
    is to fo from false to y ≤ x. Thus, the goal changes from false 
    to y ≤ x. -/
  rw h,
end

/- Alternatively -/
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  intro h',  
    /- In Lean, ¬ P is defined as an implication P → false.
    In this context, ¬ y ≤ x means 'y ≤ x → false'. intro h' 
    simply introduces the assumption y ≤ x and tells Lean to 
    find a contradiction. -/
  apply h.right,
    /- apply h.right (x ≠ y) changes the goal to x = y because 
    x ≠ y is eqivelant to ¬ x = y, meaning x = y → false" by the 
    definition of negation. "apply h.right (x ≠ y)" is to go from 
    false to x = y. Thus, the goal changes from false to x = y. -/
  exact le_antisymm h.left h',
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
λ h', h.right (le_antisymm h.left h')

-- END