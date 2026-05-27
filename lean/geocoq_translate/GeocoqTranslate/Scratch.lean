theorem neq_sym (A : Type) (a b : A) : a ≠ b → b ≠ a := by
  -- Assume `h_ab : a ≠ b`. Recall `a ≠ b` is notation for `¬ (a = b)`.
  intro h_ab
  -- We want to prove `b ≠ a`, which is `¬ (b = a)`.
  -- To prove a negation `¬ P`, we assume `P` and derive a contradiction.
  -- So, assume `h_ba : b = a`.
  intro h_ba
  -- We have `h_ab : ¬ (a = b)` and `h_ba : b = a`.
  -- From `h_ba : b = a`, we can get `a = b` using `Eq.symm`.
  have h_eq_ab : a = b := Eq.symm h_ba
  -- Now we have `h_ab : ¬ (a = b)` and `h_eq_ab : a = b`.
  -- Applying the negation `h_ab` to the equality `h_eq_ab` yields `False`.
  exact h_ab h_eq_ab
