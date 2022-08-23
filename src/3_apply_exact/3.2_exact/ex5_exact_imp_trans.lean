import tactic 

/- 
Tactics you may consider 
-intro
-cases
-exact
-have
-clear
-/

variables P Q R :  Prop

theorem basic_logic : (P → Q) ∧ (Q → R) → (P → R) :=
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

/- Alternatively -/
example : (P → Q) ∧ (Q → R) → (P → R) :=
begin
    intros h,
    cases h with hpq hqr,
    intro hp,
    exact (hqr (hpq (hp))),
end




