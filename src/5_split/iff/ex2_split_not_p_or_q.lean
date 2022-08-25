import tactic

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
-- END