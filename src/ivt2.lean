import topology.algebra.ordered
import topology.instances.real

-- `set_of_is_preconnected_eq_of_ordered` is the useful lemma
variables {X : Type} [topological_space X] [preconnected_space X]

#check @set_of_is_preconnected_eq_of_ordered

example (P Q R : Prop) (h : P ∨ Q ∨ R) (hQ : ¬ Q) : P ∨ R :=
or.cases_on h or.inl (λ h', or.inr (or.resolve_left h' hQ))

-- Shorter IVT-ish
example (f : X → ℝ) (hf : continuous f) (a b : X) (r : ℝ) (ha : f a < r) (hb : r < f b) :
  ∃ c, f c = r :=
by_contra $ λ h,
have h : ∀ x, f x ≠ r, from not_exists.mp h,
have h₁ : disjoint (f ⁻¹' (set.Iio r)) (f ⁻¹' (set.Ioi r)) := λ t h, lt_asymm h.1 h.2,
have h₂ : set.univ ⊆ (f ⁻¹' (set.Iio r)) ∪ (f ⁻¹' (set.Ioi r)) := set.univ_subset_iff.mpr 
  (set.eq_univ_of_forall (λ x, or.cases_on (lt_trichotomy r (f x)) or.inr 
    (λ h', or.inl (or.resolve_left h' (h x).symm)))),
let ⟨_, hx⟩ := is_preconnected_univ _ _ (continuous.is_open_preimage hf _ is_open_Iio) 
    (continuous.is_open_preimage hf _ is_open_Ioi) h₂ ⟨a, by rwa set.univ_inter⟩ ⟨b, by rwa set.univ_inter⟩ in
h₁ $ by rwa set.univ_inter at hx
