import data.real.basic
#check pow_two_nonneg

variables {x y : ℝ}

-- BEGIN
example (h : y > x^2) : y > 0 ∨ y < -1 :=
begin
  left, 
  linarith [pow_two_nonneg x],
end

example (h : -y > x^2 + 1) : y > 0 ∨ y < -1 :=
begin
  right, 
  linarith [pow_two_nonneg x],
end

--Alternatively
example (h : y > 0) : y > 0 ∨ y < -1 :=
or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
or.inr h
-- END