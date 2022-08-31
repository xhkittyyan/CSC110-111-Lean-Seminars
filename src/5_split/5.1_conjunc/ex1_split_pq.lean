import tactic


example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
begin 
  split, 
  { exact hp, },
  { exact hq, },
end
