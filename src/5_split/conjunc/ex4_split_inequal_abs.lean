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

/- with le_abs_self and neg_le_abs_self, now we can proof abs_add 
using the split tactic-/
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