import data.real.basic

/- Tactics you may consider
-intro
-rw
-apply
-exact
-cal
-dsimp: definition simplification
-/

variables (f g : ℝ → ℝ)

#check mul_assoc
#check neg_mul_comm
#check neg_mul_neg
#check neg_eq_neg_one_mul 

-- BEGIN
def fn_even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def fn_odd (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

example (ef : fn_even f) (og : fn_odd g) : fn_odd (λ x, f x * g x) :=
begin 
  intro x, dsimp,
  rw [ef, og],
  rw ← neg_mul_comm,
  rw neg_eq_neg_one_mul,
  rw mul_assoc,
  rw ← neg_eq_neg_one_mul,
end

example (ef : fn_even f) (og : fn_odd g) : fn_even (λ x, f (g x)) :=
begin
  intro x,
  dsimp,
  rw og,
  rw ef,
  exact (rfl.congr (ef (g (-x)))).mpr (eq.symm (ef (-g (-x)))),
end

example (ef : fn_even f) (eg : fn_even g) : fn_even (λ x, f x + g x) :=
begin
  intro x,
  calc
    (λ x, f x + g x) x = f x + g x       : rfl
                   ... = f (-x) + g (-x) : by rw [ef, eg]
end

example (of : fn_odd f) (og : fn_odd g) : fn_even (λ x, f x * g x) :=
begin
  intro x,
  calc
    (λ x, f x * g x) x = f x * g x      : rfl
                   ... = - f (-x) * - g(-x) : by rw [of, og]
                   ... = f (-x) * g(-x)     : by rw neg_mul_neg,
end

-- END