import tactic

-- BEGIN
variables {α : Type*} [partial_order α]
variables a b : α

example : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  rw lt_iff_le_not_le,
  split,
    intro hl,
    split,
    cases hl with hl1 hl2,
    exact hl1,
    contrapose! hl,
    intro h',
    rw hl,

    intro hr,
    cases hr with hr1 hr2,
    split, 
    exact hr1,
    contrapose! hr2,
    exact le_antisymm hr1 hr2,
end
-- END