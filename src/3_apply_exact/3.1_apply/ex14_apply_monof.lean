import data.real.basic

variables (f : ℝ → ℝ) (a b : ℝ)

#check @lt_of_not_ge
#check @not_lt_of_gt

-- BEGIN
example (h : monotone f) (h' : f a < f b) : a < b :=
begin
  apply lt_of_not_ge,
  intro hab,
  have : f a ≥ f b,
    from h hab, 
  apply not_lt_of_ge this,
  exact h', 
end

example (h : a ≤ b) (h' : f b < f a) : ¬ monotone f :=
begin
  intro fmono,
  have : f a ≤ f b,
   from fmono h,
  apply not_lt_of_ge this,
  exact h',
end
-- END