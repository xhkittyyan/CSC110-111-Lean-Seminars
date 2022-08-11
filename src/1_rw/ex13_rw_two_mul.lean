import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

#check one_mul
#check add_mul
#check one_add_one_eq_two

-- BEGIN

lemma one_add_one_eq_two : 1 + 1 = (2 : R) :=
by refl

theorem two_mul (a : R) : 2 * a = a + a :=
begin
  rw ← one_add_one_eq_two,
  sorry,
end
-- END

#check one_add_one_eq_two
#check two_mul

end my_ring