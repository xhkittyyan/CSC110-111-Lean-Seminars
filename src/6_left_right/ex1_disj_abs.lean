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
-- END

#check @le_abs_self
#check @neg_le_abs_self

end my_abs