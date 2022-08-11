import data.nat.gcd

variables x y z : ℕ

#check dvd_mul_left
#check dvd_mul_right
#check @dvd_mul_of_dvd_left
#check @dvd_mul_of_dvd_right

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
dvd_trans h₀ h₁

example : x ∣ y * x * z :=
begin
  apply dvd_mul_of_dvd_left,
  apply dvd_mul_left,
end

example : x ∣ x^2 :=
by apply dvd_mul_right