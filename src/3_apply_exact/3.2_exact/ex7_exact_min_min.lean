import data.real.basic

variables a b c : ℝ

#check le_antisymm
#check le_min
#check le_trans
#check min_le_right a b 
#check min_le_left b c

-- BEGIN

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