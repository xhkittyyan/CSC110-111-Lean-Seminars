import data.real.basic

-- BEGIN
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 :=
begin
  rcases lt_trichotomy x 0 with xlt | xeq | xgt,
  { left, exact xlt },
  { contradiction },
  right, 
  exact xgt,
end

/- using the cases tactic recursively -/
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 :=
begin
  cases lt_trichotomy x 0 with xlt xle,
    left,
    exact xlt,
      cases xle with xeq xlt,
      contradiction,
    right,
    exact xlt,
end
-- END