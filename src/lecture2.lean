import lecture1

/-
Theorem 1.3 (Bolzano-Weierstrass)
-/
theorem bolzano_weierstrass {x : ℕ → ℝ} (K : ℝ) (hx : ∀ i, |x i| < K) :
  ∃ (n : ℕ → ℕ), (∀ i, n i < n (i + 1)) ∧ is_convergent (x ∘ n) :=
begin
  sorry
end
