import tactic
variables P Q : Prop 

open_locale classical

-- BEGIN
example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
begin
  split,
    intro hpq,
      by_contra h',
      push_neg at h',
      cases h' with h'p h'nq,
      apply h'nq (hpq (h'p)),
    intros hnpq hp,
      cases hnpq with hnp hq,
      contradiction,
      exact hq,
end

/- using the by_cases tactic -/
example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
begin
  split, 
    intro hpq,
      by_cases h : P,
        right, 
          exact hpq h,
        left, 
          exact h, 
    intros hnpq hp,
      cases hnpq with hnp hq,
        contradiction,
        exact hq,
end
-- END