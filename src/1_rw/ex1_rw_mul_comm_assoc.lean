import data.real.basic

variables a b c : ℝ

#check mul_comm b a
#check mul_assoc c b a

example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b, 
  /- mul_comm a b refers to the commutative law for multiplication 
  on a and b: a * b = b * a. 'rw mul_comm a b' tells Lean to replace
  a * b with b * a in the goal. Now the goal becomes (b * a) * c = 
  b * (a * c). -/
  
  rw mul_assoc b a c,
  /- mul_assoc b a c refers to the associative law for multiplication 
  on b, a, and c: b * a * c = b * (a * c). Note that Lean leaves out 
  parentheses when possible. Since multiplication is left-associative,
  the left-hand side of mul_assoc b * a * c refers to (b * a) * c. 
  'rw mul_assoc b a c' solves the goal b * a * c = b * (a * c), and hence, 
  completes the proof. -/
end