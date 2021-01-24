import topology.instances.real
import topology.basic
import topology.algebra.group
import tactic

open_locale filter topological_space
open filter

notation `|` x `|` := abs x

/-
First, we shall define the definition of convergence of a sequence. mathlib uses filters, so
we will show the filter statement and the common definition are in fact equivalent. We state the
theorems in terms of filters so that we can use the lemmas from mathlib as well when we don't want
to prove them.
-/
lemma tendsto_seq_iff (x : ℕ → ℝ) (c : ℝ) :
  tendsto x at_top (𝓝 c) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - c| < ε :=
begin
  split,
  { rintros h ε (hε : 0 < ε),
    let S := set.Ioo (c - ε) (c + ε),
    have hS : S ∈ 𝓝 c,
    { apply Ioo_mem_nhds;
      linarith },
    rw tendsto_def at h,
    specialize h S hS,
    rw mem_at_top_sets at h,
    cases h with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    cases hN with h1 h2,
    rw abs_lt,
    split;
    linarith },
  { intros h S hS,
    rw mem_nhds_iff_exists_Ioo_subset at hS,
    rcases hS with ⟨l, u, ⟨h1, h2⟩, h3⟩,
    let ε := min (c - l) (u - c),
    have hε : 0 < ε,
    { apply lt_min;
      linarith },
    cases h ε hε with N hN,
    rw [mem_map, mem_at_top_sets],
    use N,
    intros n hn,
    specialize hN n hn,
    rw abs_lt at hN,
    cases hN,
    apply h3,
    split,
    { have : ε ≤ c - l,
      { exact min_le_left _ _ },
      linarith },
    { have : ε ≤ u - c,
      { exact min_le_right _ _ },
      linarith } }
end .

/-
Definition of the Supremum

stuff
-/

/--
We say that a sequence xₙ is convergent if there exists a such that xₙ → a as n → ∞
-/
def is_convergent (x : ℕ → ℝ) := ∃ a, tendsto x at_top (𝓝 a)

lemma is_convergent_of_increasing_of_bdd_above {x : ℕ → ℝ} (A : ℝ) (hx₁ : ∀ n, x n ≤ x (n + 1)) 
  (hx₂ : ∀ n, x n ≤ A) : is_convergent x :=
begin
  set c := Sup (x '' set.univ) with hc,
  use c,
  rw tendsto_seq_iff,
  intros ε hε,
  have : ∃ N, c - ε < x N,
  { by_contra h,
    push_neg at h,
    have := @real.Sup_le_ub (x '' set.univ) _ (c - ε) _,
    { linarith },
    use [x 0, 0, set.mem_univ 0],
    rintros y ⟨N, hN₁, rfl⟩,
    apply h },
  cases this with N hN,
  use N,
  intros n hn,
  have hxn : x N ≤ x n,
  { exact monotone_of_monotone_nat hx₁ hn },
  have hxn' : x n ≤ c,
  { apply real.le_Sup _ _ _,
    { use A,
      rintros y ⟨k, hk, rfl⟩,
      apply hx₂ },
    use [n, set.mem_univ n] },
  rw abs_sub_lt_iff,
  split;
  linarith
end

lemma is_convergent_of_decreasing_of_bdd_below {x : ℕ → ℝ} (A : ℝ) (hx₁ : ∀ n, x (n + 1) ≤ x n) 
  (hx₂ : ∀ n, A ≤ x n) : is_convergent x := 
begin
  set c := Inf (x '' set.univ) with hc,
  use c,
  rw tendsto_seq_iff,
  intros ε hε,
  have : ∃ N, x N < c + ε,
  { by_contra h,
    push_neg at h,
    have := @real.lb_le_Inf (x '' set.univ) _ (c + ε) _,
    { linarith },
    use [x 0, 0, set.mem_univ 0],
    rintros y ⟨N, hN₁, rfl⟩,
    apply h },
  cases this with N hN,
  use N,
  intros n hn,
  have hxn : x n ≤ x N,
  { induction hn with k ih₁ ih₂,
    { refl },
    { exact le_trans (hx₁ _) ih₂ } },
  have hxn' : c ≤ x n,
  { apply real.Inf_le,
    { use A,
      rintros y ⟨k, hk, rfl⟩,
      apply hx₂ },
    use [n, set.mem_univ n] },
  rw abs_sub_lt_iff,
  split;
  linarith
end

/-
Lemma 1.1 (i)

Limits are unique. If xₙ → a and xₙ → b, then a = b
-/
lemma tendsto_at_top_nhds_unique {x : ℕ → ℝ} {a b : ℝ} (ha : tendsto x at_top (𝓝 a)) 
  (hb : tendsto x at_top (𝓝 b)) : a = b :=
begin
  have key : ∀ ε > 0, |a - b| ≤ 2 * ε,
  { rintros ε (hε : 0 < ε),
    rw tendsto_seq_iff at *,
    cases ha ε hε with N₁ hN₁,
    cases hb ε hε with N₂ hN₂,
    let N := max N₁ N₂,
    specialize hN₁ N (le_max_left _ _),
    specialize hN₂ N (le_max_right _ _),
    rw [show a - b = (a - x N) + (x N - b), by ring],
    refine le_trans (abs_add _ _) _,
    rw abs_sub,
    linarith },
  by_contra hc,
  set ε := |a - b|/3 with hεdef,
  have hab: 0 < |a - b|,
  { rwa [abs_pos, sub_ne_zero] },
  have hε : 0 < ε,
  { linarith },
  specialize key ε hε,
  rw hεdef at key,
  linarith,
end

/-
Lemma 1.1 (ii)

If xₙ → a, and x_{n_j} is a subsequence, then it will also tend to a
-/
lemma tendsto_subseq {x : ℕ → ℝ} {a : ℝ} {n : ℕ → ℕ} (hn : ∀ k, n k < n (k+1)) 
  (hx : tendsto x at_top (𝓝 a)) : tendsto (x ∘ n) at_top (𝓝 a) :=
begin
  have : ∀ k, k ≤ n k,
  { intro k,
    induction k with d ih,
    { exact nat.zero_le _ },
    exact lt_of_le_of_lt ih (hn _) },
  rw tendsto_seq_iff at *,
  intros ε hε,
  cases hx ε hε with N hN,
  use N,
  intros k hk,
  rw function.comp_apply,
  apply hN,
  exact le_trans hk (this _),
end

/-
Lemma 1.1 (iii)

If xₙ = c for all n, then xₙ → c

NB: This is in mathlib as `tensto_const_nhds`
-/
lemma tendsto_const_at_top {c : ℝ} :
  tendsto (λ n : ℕ, c) at_top (𝓝 c) :=
begin
  intros s hs,
  rw [mem_map, mem_at_top_sets],
  use 0,
  intros b hb,
  rw set.mem_set_of_eq,
  exact mem_of_nhds hs
end

/-
Lemma 1.1 (iv)

If xₙ → a and yₙ → b, then xₙ + yₙ → a + b

NB: This is in mathlib as `filter.tendsto.add`
-/
lemma tendsto_add_at_top_nhds {x y : ℕ → ℝ} {a b : ℝ} (hx : tendsto x at_top (𝓝 a)) 
  (hy : tendsto y at_top (𝓝 b)) : tendsto (x + y) at_top (𝓝 (a + b)) :=
begin
  rw tendsto_seq_iff at *,
  intros ε hε,
  cases hx (ε/2) (half_pos hε) with N₁ hN₁,
  cases hy (ε/2) (half_pos hε) with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,
  specialize hN₁ n (le_trans (le_max_left _ _) hn),
  specialize hN₂ n (le_trans (le_max_right _ _) hn),
  rw [pi.add_apply, show x n + y n - (a + b) = (x n - a) + (y n - b), by ring],
  refine lt_of_le_of_lt (abs_add _ _) _,
  linarith,
end

/-
Lemma 1.1 (v)

If xₙ → a and yₙ → b, then xₙyₙ → ab

NB: This is in mathlib as `filter.tendsto.mul`
-/
lemma tendsto_mul_at_top_nhds {x y : ℕ → ℝ} {a b : ℝ} (hx : tendsto x at_top (𝓝 a)) 
  (hy : tendsto y at_top (𝓝 b)) : tendsto (x * y) at_top (𝓝 (a * b)) :=
begin
  rw tendsto_seq_iff at *,
  intros ε hε,
  have h1 : 0 < |a| + |b| + 1,
  { linarith [abs_nonneg a, abs_nonneg b] },
  have hε' : 0 < ε / (|a| + |b| + 1) := div_pos hε h1,
  cases hx 1 zero_lt_one with N₁ hN₁,
  cases hx _ hε' with N₂ hN₂,
  cases hy _ hε' with N₃ hN₃,
  use max (max N₁ N₂) N₃,
  intros n hn,
  rw [pi.mul_apply, show x n * y n - a * b = x n * (y n - b) + (x n - a) * b, by ring],
  refine lt_of_le_of_lt (abs_add _ _) _,
  rw [abs_mul, abs_mul],
  specialize hN₁ n (le_trans (le_max_left _ _) (le_trans (le_max_left (max N₁ N₂) N₃) hn)),
  specialize hN₂ n (le_trans (le_max_right _ _) (le_trans (le_max_left (max N₁ N₂) N₃) hn)),
  specialize hN₃ n (le_trans (le_max_right _ _) hn),
  have : |x n| < |a| + 1,
  { rw abs_lt at hN₁ ⊢,
    cases hN₁ with h1 h2,
    by_cases ha : 0 ≤ a,
    { rw abs_of_nonneg ha,
      split; linarith },
    { rw not_le at ha,
      rw abs_of_neg ha,
      split; linarith } },
  calc |x n| * |y n - b| + |x n - a| * |b| ≤ (|a| + 1) * |y n - b| + |x n - a| * |b| : _
                                       ... < (|a| + 1) * (ε / (|a| + |b| + 1)) + ε / (|a| + |b| + 1) * |b| : _
                                       ... = ε : _,
  { apply add_le_add_right,
    apply mul_le_mul,
    { exact le_of_lt this },
    { refl },
    { exact abs_nonneg _ },
    { linarith [abs_nonneg a] } },
  { apply add_lt_add_of_lt_of_le,
    { rwa mul_lt_mul_left,
      linarith [abs_nonneg a] },
    { apply mul_le_mul,
      { exact le_of_lt hN₂ },
      { refl },
      { exact abs_nonneg _ },
      { exact le_of_lt (lt_of_le_of_lt (abs_nonneg _) hN₂) } } },
    { field_simp,
      apply div_eq_of_eq_mul,
      { linarith },
      ring }
end .

/-
Lemma 1.1 (vi)

If xₙ → a, ∀ n, xₙ ≠ 0, a ≠ 0 then 1/aₙ → 1/a

NB: This is in mathlib as `filter.tendsto.inv`
-/
lemma tendsto_inv_at_top_nhds {x : ℕ → ℝ} {a : ℝ} (hx₁ : ∀ n, x n ≠ 0) (ha : a ≠ 0)
  (hx₂ : tendsto x at_top (𝓝 a)) : tendsto x⁻¹ at_top (𝓝 a⁻¹) :=
begin
  rw tendsto_seq_iff at *,
  intros ε hε,
  have hε' : 0 < |a|^2 * ε / 2,
  { apply div_pos,
    { apply mul_pos,
      { apply pow_two_pos_of_ne_zero,
        apply ne_of_gt,
        apply abs_pos.mpr ‹_› },
      { exact hε } },
    { norm_num } },
  cases hx₂ (|a|/2) (div_pos (abs_pos.mpr ha) zero_lt_two) with N₁ hN₁,
  have hN₁ : ∀ n ≥ N₁, |a|/2 ≤ |x n|,
  { intros n hn,
    specialize hN₁ n hn,
    rw abs_sub_lt_iff at hN₁,
    by_cases hx : 0 ≤ x n; [rw abs_of_nonneg hx at *, { rw not_le at hx, rw abs_of_neg hx at * }];
    { by_cases ha' : 0 ≤ a,
      { rw [abs_of_nonneg ha'] at *,
        linarith },
      { rw [not_le] at ha',
        rw [abs_of_neg ha'] at *,
        linarith } } },
  cases hx₂ _ hε' with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,
  specialize hN₁ n (le_of_max_le_left hn),
  rw div_le_iff at hN₁,
  specialize hN₂ n (le_of_max_le_right hn),
  rw [pi.inv_apply, inv_sub_inv (hx₁ _) ha, abs_div, abs_sub, div_lt_iff, abs_mul],
  calc |x n - a| < |a|^2 * ε / 2 : hN₂
             ... ≤ ε * (|x n| * |a|) : _,
  rwa [div_le_iff, pow_two, mul_comm, mul_assoc, mul_le_mul_left hε, mul_right_comm, 
      mul_le_mul_right (abs_pos.mpr ha)],
  { norm_num },
  { rw abs_mul,
    apply mul_pos,
    { exact abs_pos.mpr (hx₁ n) },
    { exact abs_pos.mpr ha } },
  { norm_num },
end .

/-
Lemma 1.1 (vii)

If xₙ ≤ A, and xₙ → a, then a ≤ A 
-/
lemma tendsto_lim_le_of_le {x : ℕ → ℝ} {a A : ℝ} (hx₁ : ∀ n, x n ≤ A) 
  (hx₂ : tendsto x at_top (𝓝 a)) : a ≤ A :=
begin
  by_contra h,
  rw not_le at h,
  set ε := a - A with hε,
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
Lemma 1.2

1/n → 0
-/
lemma tensto_one_div : tendsto (λ n, 1/(n + 1) : ℕ → ℝ) at_top (𝓝 0) :=
begin
  have h1 : ∃ a, tendsto (λ n, 1/(n + 1) : ℕ → ℝ) at_top (𝓝 a) := is_convergent_of_decreasing_of_bdd_below 0 _ _,
  cases h1 with a ha,
  have h2 : tendsto (λ n, 1/2 * (1/(n+1)) : ℕ → ℝ) at_top (𝓝 (1/2 * a)),
  { apply filter.tendsto.mul,
    { exact tendsto_const_nhds },
    { exact ha } },
  have h3 : tendsto (λ n, 1/2 * (1/(n+1)) : ℕ → ℝ) at_top (𝓝 a),
  { have : (λ n, 1/2 * (1/(n+1) : ℝ) : ℕ → ℝ) = (λ n, 1/(n + 1) : ℕ → ℝ) ∘ (λ n, 2 * n + 1 : ℕ → ℕ),
    { ext n,
      simp only [←mul_inv', mul_add, one_div, mul_one, nat.cast_bit0, inv_inj', nat.cast_add, nat.cast_one, nat.cast_mul],
      linarith, },
    rw this,
    apply tendsto_subseq,
    { intro k, omega },
    { exact ha } },
  have h4 : a = 1/2 * a,
  { exact tendsto_at_top_nhds_unique h3 h2 },
  have h5 : a = 0,
  { linarith },
  rw h5 at *,
  exact ha,
  { intro n,
    rw one_div_le_one_div,
    { norm_num },
    { linarith [@nat.cast_add ℝ _ _ n 1, @nat.cast_one ℝ _ _, @nat.cast_nonneg ℝ _ n] },
    { linarith [@nat.cast_nonneg ℝ _ n] } },
  intro n,
  apply le_of_lt,
  apply div_pos,
  { exact zero_lt_one },
  { linarith [@nat.cast_nonneg ℝ _ n] },
end .

/-
Remark: The definition of convergence of a sequence holds just as well for ℂ as it does for ℝ, that
is, we can define the convergence of xₙ ∈ ℂ just as well as xₙ ∈ ℝ
-/
