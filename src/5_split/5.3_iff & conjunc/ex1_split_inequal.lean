import data.real.basic

-- BEGIN
example {x y : ℝ} : x ≤ y ∧ ¬ y ≤ x ↔ x ≤ y ∧ x ≠ y :=
begin
  split,
    intro hl,
    cases hl with hl1 hl2,
    split,
    exact hl1,
    contrapose! hl2,
    rw hl2,
    
    intro hr,
    cases hr with hr1 hr2,
    split, 
    exact hr1,
    contrapose! hr2,
    exact le_antisymm hr1 hr2,
end
-- END