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
  /- assume that the negation of Q is true:
    "h' : ¬ Q" and prove it false -/
  exact h h',
  /- A contradiction is found in h and h' -/
end

example (h : Q) : ¬ ¬ Q :=
begin
  by_contra h',
  contradiction,
end
-- END

/- Tactic Proof 1: Double negation -/
example (P : Prop) : ¬ ¬ P → P :=
begin
  intro hnnp,
  /- introduce the proof of ¬¬P, denoted as hnnp -/
  by_contra h,
  /- 'by_contra h' creates the negation of what is to 
     be proved, namely h: ¬P, and tells Lean to prove
     false by finding a contradiction -/
  exact hnnp h,
  /- A contradiction is found in hnnp (¬¬P) and h (¬P):  
     they cannot be true at the same time -/
end

/- Tactic Proof 2: Double negation -/
example (P : Prop) : ¬ ¬ P → P :=
begin
  intro hnnp,
  /- introduce the proof of ¬¬P, denoted as hnnp. -/
  by_contra h, 
  /- 'by_contra h' creates the negation of what is to 
     be proved, namely h: ¬P, and tells Lean to prove
     false by finding a contradiction. -/
  apply hnnp,
  /- ¬¬P is equivalent to ¬P → false. The apply tactic 
     transforms the current goal to sufficient conditions. 
     'apply hnnp' (hnnp: ¬¬P) matches the goal ⊢ false 
     and leaves the hypothesis ¬P as a new goal. As a 
     result, the goal changes from ⊢ false to ⊢ ¬P. -/
  exact h,
  /- use the proof of ¬P (h) to prove ¬P. -/
end

/- Tactic Proof 3: Double negation -/
example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  by_cases h' : P,
  { assumption },
  contradiction,
end

/- Tactic Proof 4: Double negation -/
example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  change ¬P → false at h,
  by_contra hP,
  apply h,
  exact hP,
end

/- Tactic Proof 5: Double negation -/
example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases classical.em P,
  { assumption },
  contradiction
end

/- Term Proof 1: Double negation -/
example (P : Prop) (h : ¬ ¬ P) : P :=
by_contradiction
  (assume h1 : ¬ P,
    show false, from h h1)

open classical
/- Term Proof 2: Double negation -/
example (P : Prop) (h : ¬ ¬ P) : P :=
by_cases
  (assume h1 : P, h1)
  (assume h1 : ¬ P, absurd h1 h)