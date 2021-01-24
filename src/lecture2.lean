import lecture1

open_locale filter topological_space
open filter

open_locale classical
noncomputable theory

lemma sandwich {x y z : ℕ → ℝ} {t : ℝ} (hx : tendsto x at_top (𝓝 t)) (hz : tendsto z at_top (𝓝 t))
  (hxy : ∀ n, x n ≤ y n) (hyz : ∀ n, y n ≤ z n) : tendsto y at_top (𝓝 t) :=
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
Theorem 1.3 (Bolzano-Weierstrass)
-/
namespace bolzano_weierstrass

lemma step_aux {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b) 
  (hx : set.infinite {n | x n ∈ set.Icc a b}) :
  set.infinite {n | x n ∈ set.Icc a ((a+b)/2)} ∨ set.infinite {n | x n ∈ set.Icc ((a+b)/2) b} :=
begin
  by_contra h,
  push_neg at h,
  rw [set.infinite, set.infinite, not_not, not_not] at h,
  apply hx,
  have : {n | x n ∈ set.Icc a b} = {n | x n ∈ set.Icc a ((a+b)/2)} ∪ {n | x n ∈ set.Icc ((a+b)/2) b},
  { ext k,
    simp only [set.mem_union_eq, set.mem_set_of_eq, set.mem_Icc],
    split,
    { rintro ⟨h1, h2⟩,
      by_cases h' : x k ≤ (a + b)/ 2,
      { left, split; linarith },
      { right, split; linarith } },
    { rintro (⟨h1,h2⟩|⟨h1, h2⟩);
      split;
      linarith } },
  rw this,
  refine set.finite.union h.1 h.2,
end

def step (x : ℕ → ℝ) (a b : ℝ) : ℝ × ℝ :=
if set.infinite {n | x n ∈ set.Icc a ((a+b)/2)} then
  (a, (a + b)/2)
else
  ((a + b)/2, b)

lemma step_valid (x : ℕ → ℝ) {a b : ℝ} (h : a ≤ b) :
  let p := step x a b in
  p.1 ≤ p.2 :=
begin
  dsimp [step],
  split_ifs with hp hp; linarith
end

lemma step_valid' {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b) 
  (hx : set.infinite {n | x n ∈ set.Icc a b}) :
  let p := step x a b in
  set.infinite {n | x n ∈ set.Icc p.1 p.2} :=
begin
  dsimp [step],
  split_ifs with hp hp,
  { exact hp },
  { exact or.resolve_left (step_aux h hx) hp }
end

lemma step_valid'' (x : ℕ → ℝ) {a b : ℝ} (h : a ≤ b) :
  let p := step x a b in
  a ≤ p.1 :=
begin
  dsimp [step],
  split_ifs with hp hp,
  { refl },
  { linarith }
end

lemma step_valid''' (x : ℕ → ℝ) {a b : ℝ} (h : a ≤ b) :
  let p := step x a b in
  p.2 ≤ b :=
begin
  dsimp [step],
  split_ifs with hp hp,
  { linarith },
  { refl },
end

lemma step_valid'''' (x : ℕ → ℝ) {a b : ℝ} :
  let p := step x a b in
  p.2 - p.1 = 1/2 * (b - a) :=
begin
  dsimp [step],
  split_ifs with hp hp;
  { linarith },
end

noncomputable def step_n (x : ℕ → ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
| 0 := (a, b)
| (n + 1) := let p := step_n n in step x p.1 p.2

lemma step_n_valid (x : ℕ → ℝ) {a b : ℝ} (h : a ≤ b) (n : ℕ) :
  (step_n x a b n).1 ≤ (step_n x a b n).2 :=
begin
  induction n with k ih,
  { exact h },
  { dsimp [step_n],
    apply step_valid,
    exact ih }
end

def seq_a (x : ℕ → ℝ) (a b : ℝ) (n : ℕ) : ℝ := (step_n x a b n).1
def seq_b (x : ℕ → ℝ) (a b : ℝ) (n : ℕ) : ℝ := (step_n x a b n).2

lemma seq_a_increasing (x : ℕ → ℝ) (a b : ℝ) (ha : a ≤ b) : monotone (seq_a x a b) :=
begin
  apply monotone_of_monotone_nat,
  intro n,
  dsimp [seq_a, step_n],
  apply step_valid'',
  apply step_n_valid,
  exact ha,
end

lemma a_le_seq_a (x : ℕ → ℝ) (a b : ℝ) (ha : a ≤ b) (n : ℕ) : a ≤ seq_a x a b n :=
begin
  exact @seq_a_increasing x a b ha 0 n (nat.zero_le _),
end

lemma seq_b_decreasing (x : ℕ → ℝ) (a b : ℝ) (ha : a ≤ b) : 
  ∀ n m, n ≤ m → seq_b x a b m ≤ seq_b x a b n :=
begin
  intros n m h,
  induction h with k ih₁ ih₂,
  { refl },
  { dsimp [seq_b, step_n],
    apply le_trans _ ih₂,
    apply step_valid''',
    apply step_n_valid,
    exact ha }
end

lemma seq_b_le_b (x : ℕ → ℝ) (a b : ℝ) (ha : a ≤ b) (n : ℕ) : seq_b x a b n ≤ b :=
begin
  exact seq_b_decreasing x a b ha 0 n (nat.zero_le _),
end

lemma seq_a_le_seq_b (x : ℕ → ℝ) (a b : ℝ) (ha : a ≤ b) (n : ℕ) : seq_a x a b n ≤ seq_b x a b n :=
step_n_valid x ha n

lemma is_convergent_seq_a (x : ℕ → ℝ) (a b : ℝ) (ha : a ≤ b) : is_convergent (seq_a x a b) :=
begin
  apply is_convergent_of_increasing_of_bdd_above b,
  { intro n,
    apply seq_a_increasing,
    exact ha,
    exact nat.le_succ _ },
  { intro n,
    apply le_trans (seq_a_le_seq_b x a b ha n),
    apply seq_b_le_b,
    exact ha }
end

lemma is_convergent_seq_b (x : ℕ → ℝ) (a b : ℝ) (ha : a ≤ b) : is_convergent (seq_b x a b) :=
begin
  apply is_convergent_of_decreasing_of_bdd_below a,
  { intro n,
    apply seq_b_decreasing,
    exact ha,
    exact nat.le_succ _ },
  { intro n,
    apply le_trans _ (seq_a_le_seq_b _ _ _ _ _),
    apply a_le_seq_a,
    exact ha,
    exact ha }
end

lemma seq_b_succ_sub_seq_a_succ {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b) (n : ℕ) :
  seq_b x a b n.succ - seq_a x a b n.succ = 1/2 * (seq_b x a b n - seq_a x a b n) :=
begin
  dsimp [seq_a, seq_b, step_n],
  apply step_valid'''',
end

lemma seq_a_seq_b_limit_same {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b) (s t : ℝ)
  (hs : tendsto (seq_a x a b) at_top (𝓝 s))
  (ht : tendsto (seq_b x a b) at_top (𝓝 t)) : s = t :=
begin
  have h1 := filter.tendsto.sub ht hs,
  have h2 := @tendsto_subseq _ _ nat.succ (λ n, nat.lt_succ_self _) h1,
  have h3 : (λ n, seq_b x a b n - seq_a x a b n) ∘ nat.succ = (λ n, 1/2 *(seq_b x a b n - seq_a x a b n)),
  { ext n,
    dsimp,
    rwa seq_b_succ_sub_seq_a_succ },
  rw h3 at h2,
  have h4 := tendsto.const_mul (1/2 : ℝ) h1,
  have h5 := tendsto_at_top_nhds_unique h2 h4,
  linarith,
end

lemma step_n_valid' {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b) (hx : set.infinite {i | x i ∈ set.Icc a b}) (n : ℕ) :
  set.infinite {i | x i ∈ set.Icc (seq_a x a b n) (seq_b x a b n)} :=
begin
  induction n with k ih,
  { exact hx },
  { dsimp [seq_a, seq_b, step_n] at *,
    apply step_valid',
    { apply step_n_valid,
      apply h },
    { exact ih } }
end

lemma exists_ge_mem_Icc {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b) 
  (hx : set.infinite {i | x i ∈ set.Icc a b}) (k m : ℕ) : 
  ∃ n > k, x n ∈ set.Icc (seq_a x a b m) (seq_b x a b m) :=
begin
  have h1 := step_n_valid' h hx m,
  dsimp at h1,
  by_contra h,
  push_neg at h,
  have h2 : {i | x i ∈ set.Icc (seq_a x a b m) (seq_b x a b m)} ⊆ (finset.range (k+1) : set ℕ),
  { intros n hn,
    rw [finset.mem_coe, finset.mem_range],
    by_contra h',
    have h'' : k < n,
    { linarith },
    specialize h n h'',
    apply h,
    exact hn },
  apply h1,
  exact set.finite.subset (finset.finite_to_set _) h2,
end

noncomputable def n {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b) 
  (hx : set.infinite {i | x i ∈ set.Icc a b}) : ℕ → ℕ
| 0 := nat.find $ exists_ge_mem_Icc h hx 0 0
| (k + 1) := let p := n k in nat.find $ exists_ge_mem_Icc h hx p (k+1)

lemma n_spec {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b)
  (hx : set.infinite {i | x i ∈ set.Icc a b}) (k : ℕ) :
  x (n h hx k) ∈ set.Icc (seq_a x a b k) (seq_b x a b k) :=
begin
  cases k,
  { cases nat.find_spec (exists_ge_mem_Icc h hx 0 0) with h1 h2,
    exact h2 },
  { let p := n h hx k,
    cases nat.find_spec (exists_ge_mem_Icc h hx p (k+1)) with h1 h2,
    dsimp [seq_a, seq_b, step_n, n] at *, -- ok, this `dsimp` is necessary?
    exact h2 }
end

end bolzano_weierstrass

theorem bolzano_weierstrass {x : ℕ → ℝ} (K : ℝ) (hx : ∀ i, |x i| ≤ K) :
  ∃ (n : ℕ → ℕ), (∀ i, n i < n (i + 1)) ∧ is_convergent (x ∘ n) :=
begin
  set a := -K with ha,
  set b := K with ha,
  have hKnonneg : 0 ≤ K,
  { linarith [abs_nonneg (x 0), hx 0] },
  have hab : a ≤ b := by linarith,
  have hx' : set.infinite {i | x i ∈ set.Icc a b},
  { convert set.infinite_univ,
    { ext n,
      rw [iff_true, set.mem_Icc],
      specialize hx n,
      rw abs_le at hx,
      split; linarith },
    { exact nat.infinite } },
  use bolzano_weierstrass.n hab hx',
  split,
  { intro i,
    unfold bolzano_weierstrass.n,
    let p := bolzano_weierstrass.n hab hx' i,
    dsimp only,
    cases nat.find_spec (bolzano_weierstrass.exists_ge_mem_Icc hab hx' p (i+1)) with h1 h2,
    exact h1 },
  { cases bolzano_weierstrass.is_convergent_seq_a x a b hab with t ht,
    cases bolzano_weierstrass.is_convergent_seq_b x a b hab with r hr,
    have := bolzano_weierstrass.seq_a_seq_b_limit_same hab t r ht hr,
    rw this at *,
    use r,
    apply sandwich ht hr,
    { intro n,
      exact (bolzano_weierstrass.n_spec hab hx' n).1 },
    { intro n,
      exact (bolzano_weierstrass.n_spec hab hx' n).2 } }
end
