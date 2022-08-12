import tactic

/- Tactics you may consider
-intro
-cases
-exact
-apply
-change
-by_cases 
-by_contra
-assumption
-contradition
-/

open_locale classical

variables (P Q : Prop)

#check classical.em 
#check classical.em Q

-- BEGIN
example (h : ¬ ¬ Q) : Q :=
begin
  by_contra h', 
  /- assume that the negation of the conclusion "Q" is true:
    "h' : ¬ Q" and prove it false -/
  apply h, 
  /- apply ¬¬Q is true -/
  exact h',
end

example (h : Q) : ¬ ¬ Q :=
begin
  by_contra h',
  contradiction,
end
-- END

/- Proof 1: Double negation -/
example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  change ¬P → false at h,
  by_contra hP,
  apply h,
  exact hP,
end

/- Proof 2: Double negation -/
example (P : Prop) : ¬ ¬ P → P :=
begin
  intro hnnp,
  by_contra h', 
  apply hnnp,
  exact h',
end

/- Proof 3: Double negation -/
example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  by_cases h' : P,
  { assumption },
  contradiction,
end

/- Proof 4: Double negation -/
example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases classical.em P,
  { assumption },
  contradiction
end