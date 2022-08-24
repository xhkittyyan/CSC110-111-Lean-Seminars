import data.real.basic

#check lt_trichotomy

-- BEGIN
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 :=
begin
  cases lt_trichotomy x 0 with xlt xle,
    left,
    exact xlt,
    sorry,  
end
-- END