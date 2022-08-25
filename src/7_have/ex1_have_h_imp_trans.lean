import tactic 

variables P Q R :  Prop

example : (P → Q) ∧ (Q → R) → (P → R) :=
begin
    intros h,
    have hpq : P → Q,
    exact h.left,
    have hqr : Q → R,
    exact h.right,
    clear h,
    intro hp,
    have hq : Q,
    exact hpq hp,
    exact hqr hq,
end

-- Alternatively 
example : (P → Q) ∧ (Q → R) → (P → R) :=
begin
    intros h,
    have hpq : P → Q := h.left,
    have hqr : Q → R := h.right,
    clear h,
    intro hp,
    have hq : Q,
    exact hpq hp,
    exact hqr hq,
end

/- Alternatively, using the cases tactic -/

example : (P → Q) ∧ (Q → R) → (P → R) :=
begin
    intros h,
    cases h with hpq hqr,
    intro hp,
    exact (hqr (hpq (hp))),
end
