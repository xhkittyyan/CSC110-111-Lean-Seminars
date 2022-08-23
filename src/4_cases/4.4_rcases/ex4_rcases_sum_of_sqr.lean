import tactic

variables {α : Type*} [comm_ring α]

def sum_of_squares (x : α) := ∃ a b, x = a^2 + b^2

theorem sum_of_squares_mul {x y : α}
    (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
  sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, xeq⟩,
  rcases sosy with ⟨c, d, yeq⟩,
  rw [xeq, yeq],
  use [a*c - b*d, a*d + b*c],
  ring,
end

/- using the cases tactic recursively -/
example {x y : α}
    (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
  sum_of_squares (x * y) :=
begin
  cases sosx with a xeq,
  cases xeq with b xeqab,
    cases sosy with c yeq,
    cases yeq with d yeqcd,
    rw [xeqab, yeqcd],
    use [a*c - b*d, a*d + b*c],
    ring,
end