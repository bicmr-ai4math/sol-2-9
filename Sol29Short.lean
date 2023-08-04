import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.PGroup

variable {G : Type _} [Group G] [Fintype G]

theorem comm_of_card_4 :
    Fintype.card G = 4 → ∀ a b : G, a * b = b * a :=
  IsPGroup.commutative_of_card_eq_prime_sq (p := 2)
