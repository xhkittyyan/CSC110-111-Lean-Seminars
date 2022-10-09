import data.real.basic

/- 
Tactics you may consider 
-intro
-rw
-apply
-exact
-/

#check le_antisymm
#check mul_eq_zero.mp

-- BEGIN
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : ¬ x = y :=
begin
  intro h,
    /- In Lean, ¬ P is defined as an implication P → false.
       In this context, ¬ x = y refers to 'x = y → false'. 
       'intro h' introduces the hypothesis x = y and tells 
       Lean to find a contradiction. -/
  apply h₁,
    /- '¬ y ≤ x' is equivalent to 'y ≤ x → false' by the definition 
       of negation. The apply tactic transforms the current goal 
       to sufficient conditions. 'apply h₁' matches the goal with 
       false and leaves y ≤ x as a new goal. -/
  rw h,
    /- Replace x with y so that the goal becomes ⊢ y ≤ y. This is 
       true by le_refl: a ≤ a. And the 'rw' tactic acknowledges it. -/
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  intro h',  
    /- In Lean, ¬ P is defined as an implication 'P → false'.
       In this context, ¬ y ≤ x means 'y ≤ x → false'. intro h' 
       introduces the hypothesis y ≤ x and tells Lean to 
       find a contradiction. -/
  apply h.right,
    /- x ≠ y is eqivelant to ¬ x = y, meaning 'x = y → false' 
       by the definition of negation. The apply tactic transforms 
       the current goal to sufficient conditions. 'apply h.right 
       (x ≠ y)' matches the goal with false and leaves x = y as
       a new goal. -/
  exact le_antisymm h.left h',
    /- le_antisymm refers to 'a ≤ b → b ≤ a → a = b'; 'h.left' 
       refers to x ≤ y; and h' is the type y ≤ x. exact le_antisymm 
       h.left h' therefore solves the goal x = y. -/
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
λ h', h.right (le_antisymm h.left h')

example {a b : ℕ } : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := 
begin
  intros ha hb,
  intro hab,
    apply ha,
    


    
end 


-- END