import data.real.basic

variables {x y : ℝ}

#check le_refl
#check le_refl y
#check @le_abs 
#check @abs_le
#check neg_add
#check add_le_add

namespace my_abs

-- BEGIN
theorem le_abs_self : x ≤ abs x :=
begin
  rw le_abs,
  left,
  apply le_refl,
end

theorem neg_le_abs_self : -x ≤ abs x :=
begin
  rw le_abs,
  right,
  apply le_refl,
end

/- Alternatively -/

lemma neg_abs_le_self : - abs x ≤ x :=
begin
  nth_rewrite_rhs 0 ← neg_neg x,
  apply neg_le_neg,
  exact neg_le_abs_self,
end

theorem abs_add : abs (x + y) ≤ abs x + abs y :=
begin
  cases lt_or_le x 0 with hx hx;
  cases lt_or_le y 0 with hy hy;
  cases lt_or_le (x + y) 0 with hxy hxy;
  simp [abs_of_neg, abs_of_nonneg, hx, hy, hxy];
  linarith,
end

/- Essentially the same as the previous one, but we no longer need 
the lemma `neg_abs_le_self`. -/
example : abs (x + y) ≤ abs x + abs y :=
begin
  rw abs_eq_max_neg,
  rw max_le_iff,
  split,
  { apply add_le_add,
    exact le_abs_self,
    exact le_abs_self, },
  { rw neg_add,
    apply add_le_add,
    exact neg_le_abs_self,
    exact neg_le_abs_self, },
end

-- END

#check @le_abs_self
#check @neg_le_abs_self
#check @abs_add

end my_abs