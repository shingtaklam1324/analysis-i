import data.real.basic
import topology.continuous_on
import topology.instances.real
import topology.basic
import tactic
import lecture1

open filter
open_locale filter topological_space

/-
One alternative definition of what a countinuous function is that if xₙ → a, then f(xₙ) → f(a).

For now, we will use the mathlib definition of continuity, and show that it implies this.
-/
lemma tendsto_comp_of_continuous_at {a : ℝ} {f : ℝ → ℝ} (hf : continuous_at f a) 
  {x : ℕ → ℝ} (hx : tendsto x at_top (𝓝 a)) : tendsto (f ∘ x) at_top (𝓝 (f a)) :=
begin
  rw metric.continuous_at_iff at hf,
  rw metric.tendsto_at_top at ⊢ hx,
  intros ε hε,
  rcases hf ε hε with ⟨δ, hδpos, hδ⟩,
  rcases hx δ hδpos with ⟨N, hN⟩,
  use N,
  intros n hn,
  exact hδ (hN _ hn),
end

/-
Squeeze
-/
lemma tendsto_of_le_of_le {x y z : ℕ → ℝ} {t : ℝ} (hx : tendsto x at_top (𝓝 t)) 
  (hz : tendsto z at_top (𝓝 t)) (hxy : ∀ n, x n ≤ y n) (hyz : ∀ n, y n ≤ z n) : 
  tendsto y at_top (𝓝 t) :=
begin
  rw tendsto_seq_iff at *,
  intros ε hε,
  cases hx (ε/2) (half_pos hε) with N₁ hN₁,
  cases hz (ε/2) (half_pos hε) with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,
  specialize hxy n,
  specialize hyz n,
  specialize hN₁ n (le_of_max_le_left hn),
  specialize hN₂ n (le_of_max_le_right hn),
  rw abs_sub_lt_iff at *,
  cases hN₁ with hN₁ hN₁',
  cases hN₂ with hN₂ hN₂',
  split;
  linarith,
end

/-
If the sequence us bounded below, then so is its limit
-/
lemma tendsto_lim_le_of_le' {x : ℕ → ℝ} {a A : ℝ} (hx₁ : ∀ n, A ≤ x n) 
  (hx₂ : tendsto x at_top (𝓝 a)) : A ≤ a :=
begin
  by_contra h,
  rw not_le at h,
  set ε := A - a with hε,
  have hε' : 0 < ε,
  { linarith },
  rw tendsto_seq_iff at hx₂,
  specialize hx₂ ε hε',
  cases hx₂ with N hN,
  specialize hN N (le_refl _),
  rw abs_sub_lt_iff at hN,
  cases hN,
  specialize hx₁ N,
  linarith,
end

/-
TODO : Loosen requirement to just `hf : continuous_on f (set.Icc a b)`

Note however that with if we change just `hf`, then the statement is not true. That is, there is the
special case where c = a or c = b, and in that case, it is not true that f is continuous at a or b,
when f : ℝ → ℝ. If we instead had f : set.Icc a b → ℝ, then it would be true.
-/
lemma ivt {a b : ℝ} (h : a < b) (f : ℝ → ℝ) (hf : continuous f) (hfab : f a < f b) 
  {η : ℝ} (hη : η ∈ set.Ioo (f a) (f b)) : ∃ c ∈ set.Icc a b, f c = η :=
begin
  -- Let S be the set of all x such that f(x) < η
  let S := {x | f x < η ∧ x ∈ set.Icc a b},
  -- S is nonempty
  have hS₁ : ∃ k, k ∈ S := ⟨a, hη.1, le_refl _, le_of_lt h⟩,
  -- and bounded above, so Sup S exists.
  have hS₂ : ∃ k, ∀ x ∈ S, x ≤ k := ⟨b, λ _ ⟨_, _, hx⟩, hx⟩,
  have hbS : b ∉ S,
  { rintro ⟨h, -⟩,
    cases hη,
    linarith },
  -- Let c := Sup S.
  let c := Sup S,
  -- Then a ≤ c ≤ b
  have hac : a ≤ c := real.le_Sup _ hS₂ ⟨hη.1, le_refl _, le_of_lt h⟩,
  have hbc : c ≤ b := real.Sup_le_ub _ hS₁ (λ x ⟨_, _, hx⟩, hx),
  -- We also have that f(x) is continuous at c
  have hcontc : continuous_at f c := hf.continuous_at,
  -- Now, we claim that f(c) = η
  use c,
  refine ⟨⟨real.le_Sup S hS₂ ⟨hη.1, le_refl _, le_of_lt h⟩, hbc⟩, _⟩,
  -- We will do this by showing f(c) ≤ η, and η ≤ f(c). However the proof for η ≤ f(c) requires 
  -- f(c) ≤ η, so we prove this separately.
  have hcη : f c ≤ η,
  -- Let c₂(n) := c - 1/n
  { let c₂ : ℕ → ℝ := λ n, c - (1/(n+1)),
    -- Then c₂(n) → c as n → ∞
    have hc₂ : tendsto c₂ at_top (𝓝 c),
    { convert @filter.tendsto.sub ℕ ℝ _ _ _ (λ n, c) (λ n, 1/(n+1)) _ c 0 tendsto_const_nhds tendsto_one_div,
      exact (sub_zero _).symm, },
    -- and for all n, c₂(n) < c
    have hc₂' : ∀ n, c₂ n < c,
    { intro n,
      change c - (1/(n+1)) < c,
      simp only [one_div, sub_lt_self_iff, inv_pos],
      linarith [@nat.cast_nonneg ℝ _ n] },
    -- Then, for each n, there exists some x ∈ S such that c₂(n) < x ≤ c, as C = Sup S.
    have hc₂'' : ∀ n, ∃ x ∈ S, c₂ n < x ∧ x ≤ c,
    { intro n,
      rcases (real.lt_Sup _ hS₁ hS₂).mp (hc₂' n) with ⟨z, hz₁, hz₂⟩,
      use [z, hz₁, hz₂, real.le_Sup _ hS₂ hz₁] }, 
    -- Using this, we can define a sequence xₙ.
    let x : ℕ → ℝ := λ n, classical.some (hc₂'' n),
    -- Next, we can show that for all n, f(xₙ) < η.
    have hx₁ : ∀ n, f (x n) < η,
    { intro n,
      rcases classical.some_spec (hc₂'' n) with ⟨⟨hx : f (x n) < η, -⟩, -⟩,
      exact hx },
    -- and by the squeeze theorem, xₙ → c.
    have hx₂ : tendsto x at_top (𝓝 c),
    { apply tendsto_of_le_of_le hc₂ tendsto_const_nhds,
      { intro n,
        rcases classical.some_spec (hc₂'' n) with ⟨⟨-, -⟩, hx : c₂ n < x n, -⟩,
        exact le_of_lt hx },
      { intro n,
        rcases classical.some_spec (hc₂'' n) with ⟨⟨-, -⟩, -, hx : x n ≤ c⟩,
        exact hx } },
    -- so now we get that f(xₙ) → f(c) and f(c) ≤ η.
    apply tendsto_lim_le_of_le,
    { intro n,
      apply le_of_lt (hx₁ n) },
    { exact tendsto_comp_of_continuous_at hcontc hx₂ } },
  -- Now, all we need to do is to show that η ≤ f(c).
  { apply le_antisymm hcη,
    have hc₁ : c ≤ b,
    { apply real.Sup_le_ub _ hS₁,
      rintros x ⟨-, -, hx⟩,
      exact hx },
    have hc₂ : c < b,
    { apply lt_of_le_of_ne hc₁,
      intro h,
      have : f b ≤ η,
      { rwa h at hcη },
      cases hη,
      linarith },
    have hbc : 0 < b - c,
    { linarith },
    cases exists_nat_one_div_lt hbc with n hn,
    let x : ℕ → ℝ := λ i, c + 1/(n + i + 1),
    have hx₁ : tendsto x at_top (𝓝 c),
    { convert @filter.tendsto.add ℕ ℝ _ _ _ (λ i, c) (λ i, 1/(n+i+1)) _ c 0 tendsto_const_nhds _,
      { exact (add_zero _).symm },
      convert @tendsto_subseq _ _ (λ i, n + i) _ tendsto_one_div,
      { ext j,
        change (1/(n+j+1) : ℝ) = 1/((n+j : ℕ)+1),
        rw [nat.cast_add] },
      intro k,
      dsimp only,
      rw ←add_assoc,
      exact nat.lt_succ_self _ },
    have hx₂ : ∀ i, x i ∈ set.Icc a b,
    { intro i,
      split,
      { change a ≤ c + 1/(n + i + 1),
        have h₁: a ≤ c := real.le_Sup _ hS₂ ⟨hη.1, le_refl _, le_of_lt h⟩,
        have h₂ : (0 : ℝ) < 1/(n + i + 1),
        { rw one_div_pos,
          linarith [@nat.cast_nonneg ℝ _ n, @nat.cast_nonneg ℝ _ i] },
        linarith },
      { change c + 1/(n + i + 1) ≤ b,
        have : (1/(n + i + 1) : ℝ) ≤ 1/(n + 1),
        { rw one_div_le_one_div;
          linarith [@nat.cast_nonneg ℝ _ n, @nat.cast_nonneg ℝ _ i] },
        linarith } },
    have hx₃ : ∀ i, η ≤ f (x i),
    { intro i,
      by_contra hcontra,
      rw not_le at hcontra,
      have hxS : x i ∈ S,
      { exact ⟨hcontra, hx₂ i⟩ },
      have hxc : x i ≤ c,
      { exact real.le_Sup _ hS₂ hxS },
      have h₁ : (0 : ℝ) < 1/(n + i + 1),
      { rw one_div_pos,
        linarith [@nat.cast_nonneg ℝ _ n, @nat.cast_nonneg ℝ _ i] },
      change c + 1/(n+i+1) ≤ c at hxc,
      linarith },
    exact tendsto_lim_le_of_le' hx₃ (tendsto_comp_of_continuous_at hcontc hx₁), }
end
