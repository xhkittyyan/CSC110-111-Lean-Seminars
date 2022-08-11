import data.real.basic

#check le_refl
#check le_trans
#check @add_le_add

-- BEGIN

example (x : ℝ) : x ≤ x :=
begin
  apply le_refl,
end  

/- in this context, the apply and exact tactics are equivalent -/
example (x : ℝ) : x ≤ x :=
begin
  exact le_refl x,
end  

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  apply le_trans,
  { apply h₀ },
  apply h₁,
end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  apply le_trans h₀,
  apply h₁,
end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin 
  apply le_trans h₀ h₁,
end  

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  exact le_trans h₀ h₁,
end 

-- END