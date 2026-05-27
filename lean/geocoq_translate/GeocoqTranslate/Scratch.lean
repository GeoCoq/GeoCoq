theorem neq_sym (A : Type) (a b : A) : a ≠ b → b ≠ a := by
  intro h_ne_ab  -- Assume h_ne_ab : a ≠ b, which is ¬(a = b)
  intro h_eq_ba  -- Assume h_eq_ba : b = a. Our goal is to derive False.
  -- We have ¬(a = b) and we need to produce a contradiction by showing a = b.
  -- From h_eq_ba : b = a, we can use Eq.symm to get a = b.
  have h_eq_ab : a = b := Eq.symm h_eq_ba
  -- Now we have h_ne_ab : ¬(a = b) and h_eq_ab : a = b.
  -- Applying h_ne_ab (which is a function from (a = b) to False) to h_eq_ab
  -- yields False, which completes the proof.
  exact h_ne_ab h_eq_ab
