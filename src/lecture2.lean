import lecture1

open_locale filter topological_space big_operators
open filter

open_locale classical
noncomputable theory

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
Theorem 1.3 (Bolzano-Weierstrass)

To prove this, we are going to use the proof given in lecture, that is, the one by halving the
interval every time, and showing that we have an infinite number of elements no matter how small
the interval becomes.
-/
namespace bolzano_weierstrass

/-
First, we define the inductive step. That is, given an interval [a, b], this returns either 
  [a, (a+b)/2] or [(a+b)/2, b], depending on whether there is an infinite number of xₙ in the first
  interval.
-/
def step (x : ℕ → ℝ) (a b : ℝ) : ℝ × ℝ :=
if set.infinite {n | x n ∈ set.Icc a ((a+b)/2)} then
  (a, (a + b)/2)
else
  ((a + b)/2, b)

/-
First, we show that the result of `step` still forms a well defined interval.
-/
lemma step_valid (x : ℕ → ℝ) {a b : ℝ} (h : a ≤ b) :
  let p := step x a b in
  p.1 ≤ p.2 :=
begin
  dsimp [step],
  split_ifs with hp hp; linarith
end

/-
Then, we show that the resulting interval still contains an infinite number of xₙs. To show this,
note that it is not possible for both intervals to be finite, as their union is the original 
interval, and if they are both finite then so is their union. Contradiction.
-/
lemma step_valid'_aux {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b) 
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

lemma step_valid' {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b) 
  (hx : set.infinite {n | x n ∈ set.Icc a b}) :
  let p := step x a b in
  set.infinite {n | x n ∈ set.Icc p.1 p.2} :=
begin
  dsimp [step],
  split_ifs with hp hp,
  { exact hp },
  { exact or.resolve_left (step_valid'_aux h hx) hp }
end

/-
Next, we show that the new interval is contained within the previous interval
-/
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

/-
Finally, we show that the size of the new interval is half the size of the original interval.
-/
lemma step_valid'''' (x : ℕ → ℝ) {a b : ℝ} :
  let p := step x a b in
  p.2 - p.1 = 1/2 * (b - a) :=
begin
  dsimp [step],
  split_ifs with hp hp;
  { linarith },
end

/-
Then, we define the sequence of intervals. [a, b], [a₁, b₁], ...
-/
noncomputable def step_n (x : ℕ → ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
| 0 := (a, b)
| (n + 1) := let p := step_n n in step x p.1 p.2

/-
We can show that the nth term of this is still a well defined sequence, by induction and the fact
that we have already proven this for `step`.
-/
lemma step_n_valid (x : ℕ → ℝ) {a b : ℝ} (h : a ≤ b) (n : ℕ) :
  (step_n x a b n).1 ≤ (step_n x a b n).2 :=
begin
  induction n with k ih,
  { exact h },
  { dsimp [step_n],
    apply step_valid,
    exact ih }
end

/-
We then define two sequences aₙ and bₙ, which are the lower and upper bounds of those intervals
respectively.
-/
def seq_a (x : ℕ → ℝ) (a b : ℝ) (n : ℕ) : ℝ := (step_n x a b n).1
def seq_b (x : ℕ → ℝ) (a b : ℝ) (n : ℕ) : ℝ := (step_n x a b n).2

/-
We note that aₙ is increasing, that is, a₀ ≤ a₁ ≤ a₂ ≤ ...
-/
lemma seq_a_increasing (x : ℕ → ℝ) (a b : ℝ) (ha : a ≤ b) : monotone (seq_a x a b) :=
begin
  apply monotone_of_monotone_nat,
  intro n,
  dsimp [seq_a, step_n],
  apply step_valid'',
  apply step_n_valid,
  exact ha,
end

/-
As a corollary, this means that the aₙ are bounded below by a₀ = a
-/
lemma a_le_seq_a (x : ℕ → ℝ) (a b : ℝ) (ha : a ≤ b) (n : ℕ) : a ≤ seq_a x a b n :=
begin
  exact @seq_a_increasing x a b ha 0 n (nat.zero_le _),
end

/-
We also note that bₙ is decreasing, that is b₀ ≥ b₁ ≥ ...
-/
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

/-
And it follows that bₙ are bounded above by b₀ = b
-/
lemma seq_b_le_b (x : ℕ → ℝ) (a b : ℝ) (ha : a ≤ b) (n : ℕ) : seq_b x a b n ≤ b :=
begin
  exact seq_b_decreasing x a b ha 0 n (nat.zero_le _),
end

/-
An alternative statement for `step_n_valid` is that `aₙ ≤ bₙ` for all `n`.
-/
lemma seq_a_le_seq_b (x : ℕ → ℝ) (a b : ℝ) (ha : a ≤ b) (n : ℕ) : seq_a x a b n ≤ seq_b x a b n :=
step_n_valid x ha n

/-
Then, aₙ is an increasing sequence, bounded above by `b`, so it must converge.
-/
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

/-
Similarly, bₙ is a decreasing sequence that is bounded below, and it must converge as well.
-/
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

/-
An alternative statement of the halving of the sizes of the inverals is that 
  bₙ₊₁ - aₙ₊₁ = 1/2 (bₙ - aₙ) 
-/
lemma seq_b_succ_sub_seq_a_succ {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b) (n : ℕ) :
  seq_b x a b n.succ - seq_a x a b n.succ = 1/2 * (seq_b x a b n - seq_a x a b n) :=
begin
  dsimp [seq_a, seq_b, step_n],
  apply step_valid'''',
end

/-
Then we get that aₙ and bₙ must tend to the same limit. To see this, suppose if aₙ → s and bₙ → t,
then bₙ - aₙ → s - t. As a result, bₙ₊₁ - aₙ₊₁ → 1/2 (s - t) from the above. However, bₙ₊₁ - aₙ₊₁
is also a subsequence of bₙ - aₙ, so it must tend to the same limit. Thus, 1/2 (s - t) = (s - t),
and s = t.
-/
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

/-
We can then prove that there are infinitely many `n` such that xₙ ∈ [aᵢ, bᵢ] for all i.
-/
lemma step_n_valid' {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b) (hx : set.infinite {i | x i ∈ set.Icc a b}) 
  (n : ℕ) : set.infinite {i | x i ∈ set.Icc (seq_a x a b n) (seq_b x a b n)} :=
begin
  induction n with k ih,
  { exact hx },
  { dsimp [seq_a, seq_b, step_n] at *,
    apply step_valid',
    { apply step_n_valid,
      apply h },
    { exact ih } }
end

/-
From this, the set of such `n` mustn't be bounded above. So no matter gow large `k` is, there is
always an `n > k` such that xₙ ∈ [aᵢ, bᵢ]
-/
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

/-
We define `nᵢ` such that `nᵢ₊₁ > nᵢ` and that `x_nᵢ ∈ [aᵢ, bᵢ]` for all `i`. We have shown that such
nᵢ always exists so this is well defined.
-/
noncomputable def n {x : ℕ → ℝ} {a b : ℝ} (h : a ≤ b) 
  (hx : set.infinite {i | x i ∈ set.Icc a b}) : ℕ → ℕ
| 0 := nat.find $ exists_ge_mem_Icc h hx 0 0
| (k + 1) := let p := n k in nat.find $ exists_ge_mem_Icc h hx p (k+1)

/-
Finally, we show that `n` satisfies the properties outlined above.
-/
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

/-
Now that we have this, Bolzano-Weierstrass is fairly straightforward. As each of the 
`x_nᵢ ∈ [aᵢ, bᵢ]`, aᵢ ≤ x_nᵢ ≤ bᵢ, and that we've shown that aᵢ and bᵢ converge to the same limit,
so x_nᵢ must converge to the same limit as well.
-/
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
    apply tendsto_of_le_of_le ht hr,
    { intro n,
      exact (bolzano_weierstrass.n_spec hab hx' n).1 },
    { intro n,
      exact (bolzano_weierstrass.n_spec hab hx' n).2 } }
end .

/-
Definition of a Cauchy Sequence
-/
lemma cauchy_seq_iff (x : ℕ → ℝ) :
  cauchy_seq x ↔ ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m → |x n - x m| < ε :=
metric.cauchy_seq_iff

/-
Lemma 1.4

Every convergent sequence is Cauchy
-/
lemma cauchy_seq_of_is_convergent {x : ℕ → ℝ} (hx : is_convergent x) : cauchy_seq x :=
begin
  rw cauchy_seq_iff,
  intros ε hε,
  cases hx with a ha,
  rw tendsto_seq_iff at ha,
  cases ha (ε/2) (half_pos hε) with N hN,
  use N,
  intros n m hn hm,
  have h1 := hN n hn,
  have h2 := hN m hm,
  calc |x n - x m| = |(x n - a) + (a - x m)| : by ring
               ... ≤ |x n - a| + |a - x m| : abs_add _ _
               ... = |x n - a| + |x m - a| : by rw abs_sub a
               ... < ε : by linarith
end

/-
Theorem 1.5

Every Cauchy sequence is convergent
-/

/-
First, we shall show that every Cauchy sequence is bounded.
-/
lemma bdd_of_is_cauchy {x : ℕ → ℝ} (hx : cauchy_seq x) : ∃ k, ∀ n, |x n| ≤ k :=
begin
  rw cauchy_seq_iff at hx,
  cases hx 1 zero_lt_one with N₁ hN₁,
  have h₁ : ∀ m ≥ N₁, |x m| < |x N₁| + 1,
  { intros m hm,
    specialize hN₁ m N₁ hm (le_refl _),
    calc |x m| ≤ |x m - x N₁| + |x N₁| : _
           ... < |x N₁| + 1 : _,
    { convert abs_add _ _, ring },
    { linarith } },
  set S := (finset.range (N₁ + 1)).image (abs ∘ x) with hSdef,
  have hS : S.nonempty,
  { refine finset.nonempty.image _ (abs ∘ x),
    use 0,
    simp only [nat.succ_pos', finset.mem_range] },
  set k := max (|x N₁| + 1) (S.max' hS) with hk,
  use k,
  intro n,
    cases lt_or_le n N₁,
    { have : |x n| ≤ S.max' hS,
      { apply finset.le_max',
        rw [hSdef, finset.mem_image],
        use n,
        split,
        { rw [finset.mem_range], linarith },
        { refl } },
      refine le_trans this (le_max_right (|x N₁| + 1) (finset.max' S hS)) },
    { have : |x n| ≤ |x N₁| + 1,
      { apply le_of_lt,
        apply h₁,
        exact h },
      refine le_trans this (le_max_left (|x N₁| + 1) (finset.max' S hS)) }
end .

theorem is_convergent_of_is_cauchy {x : ℕ → ℝ} (hx : cauchy_seq x) : is_convergent x :=
begin
  cases bdd_of_is_cauchy hx with k hk,
  rcases bolzano_weierstrass k hk with ⟨n, h₁, ⟨a, h₂⟩⟩,
  use a,
  rw tendsto_seq_iff at ⊢ h₂,
  intros ε hε,
  rw cauchy_seq_iff at hx,
  cases hx (ε/2) (half_pos hε) with N₁ hN₁,
  cases h₂ (ε/2) (half_pos hε) with j₀ hj₀,
  use max N₁ j₀,
  intros j hj,
  calc |x j - a| ≤ |x j - x (n j)| + |x (n j) - a| : _
             ... < ε : _,
  { convert abs_add _ _,
    ring },
  { have hnj : j ≤ n j,
    { apply le_of_nat_strict_mono h₁ },
    specialize hN₁ j (n j) (le_of_max_le_left hj) (le_trans (le_of_max_le_left hj) hnj),
    specialize hj₀ j (le_of_max_le_right hj),
    simp only [function.comp_app] at hj₀,
    linarith }
end .

/-
Series

We say the sum is convergent if it the partial sums converge.
-/
def sum_convergent (x : ℕ → ℝ) := is_convergent (λ N, ∑ i in finset.range N, x i)

/-
Lemma 1.6 (i)
   ∞        ∞                                 ∞
If ∑ aₙ and ∑ bₙ both converges, then so does ∑ (αaₙ + βbₙ).
   n=1       n=1                                n=1
-/
lemma sum_convergent_add {a b : ℕ → ℝ} (ha : sum_convergent a) (hb : sum_convergent b) (α β : ℝ):
  sum_convergent (λ n, α * a n + β * b n) :=
begin
  cases ha with x hx,
  cases hb with y hy,
  use α * x + β * y,
  simp_rw [finset.sum_add_distrib, ←finset.mul_sum],
  apply tendsto.add,
  { apply tendsto.const_mul,
    exact hx },
  { apply tendsto.const_mul,
    exact hy },
end

/-
Lemma 1.6 (ii)
                                                   ∞                             ∞
If there exists N such that ∀ n ≥ N, aₙ = bₙ, then ∑ aₙ converges if and only if ∑ bₙ converges.
                                                   n=1                            n=1

The argument here is clearly symmetric, so we shall prove the implication first, and the iff
follows.
-/
lemma foo {a b : ℕ → ℝ} (h : ∃ N, ∀ n ≥ N, a n = b n)  (ha : sum_convergent a) : sum_convergent b :=
begin
  cases h with N hN,
  cases ha with x hx,
  use x - (∑ i in finset.range N, a i) + (∑ i in finset.range N, b i),
  -- have : (λ n, ∑ i in finset.range n, b i) = 
  -- λ n, (∑ i in finset.range n, a i) - (∑ i in finset.range N, a i) + (∑ i in finset.range N, b i),
  -- { ext n,
  --   simp only, },
  -- rw this,
  sorry,
end
