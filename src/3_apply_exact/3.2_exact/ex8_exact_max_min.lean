import data.real.basic

variables a b c : ℝ

#check le_antisymm
#check le_min
#check le_trans
#check max_le
#check min_le_right a b 
#check min_le_left b c
#check le_max_left
#check le_max_right

-- BEGIN

example : max a b = max b a :=
begin
  apply le_antisymm,
  { show max a b ≤ max b a,
    apply max_le,
      apply le_max_right, 
      apply le_max_left },
  { show max b a ≤ max a b, 
    apply max_le,
      apply le_max_right,
      apply le_max_left },
end

example : min (min a b) c = min a (min b c) :=
begin
  apply le_antisymm, 
  { apply le_min,
    exact le_trans (min_le_left (min a b) c) (min_le_left a b),
    apply le_min,
    exact le_trans (min_le_left (min a b) c) (min_le_right a b),
    exact min_le_right (min a b) c,
  },
  { apply le_min,
    apply le_min,
    exact min_le_left a (min b c),
    exact le_trans (min_le_right a (min b c)) (min_le_left b c),
    exact le_trans (min_le_right a (min b c)) (min_le_right b c),
  },
end
-- END