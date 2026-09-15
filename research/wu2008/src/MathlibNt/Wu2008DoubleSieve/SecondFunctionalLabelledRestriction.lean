import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledPhysicalSieve

/-! Data-preserving label restriction. No monotonicity of signed R1 is asserted. -/
namespace Wu2008DoubleSieve.LabelledPhysical.Family
open Finset
open scoped Classical
variable {α : Type*} {N : ℕ} (L : Family α N) (P : α → Prop)

noncomputable def restrictLabels : Family α N where
  labels := L.labels.filter P
  weight := L.weight
  cofactor := L.cofactor
  lower := L.lower
  upper := L.upper
  weight_nonneg := fun c hc => L.weight_nonneg c (mem_filter.mp hc).1
  geometry := fun c hc => L.geometry c (mem_filter.mp hc).1

@[simp] theorem restrictLabels_primes (c : α) :
    (L.restrictLabels P).primes c = L.primes c := rfl

theorem restrictLabels_sum_le (f : α → ℝ) (hf : ∀ c ∈ L.labels, 0 ≤ f c) :
    (∑ c ∈ (L.restrictLabels P).labels, f c) ≤ ∑ c ∈ L.labels, f c := by
  exact sum_le_sum_of_subset_of_nonneg (filter_subset P _) (fun c hc _ => hf c hc)

theorem restrictLabels_sum_partition (f : α → ℝ) :
    (∑ c ∈ L.labels, f c) = (∑ c ∈ (L.restrictLabels P).labels, f c) +
      ∑ c ∈ (L.restrictLabels (fun c => ¬P c)).labels, f c := by
  simp only [restrictLabels, sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro c _
  by_cases h : P c <;> simp [h]

theorem restrictLabels_mass_le : (L.restrictLabels P).mass ≤ L.mass := by
  exact L.restrictLabels_sum_le P _ (fun c hc =>
    mul_nonneg (L.weight_nonneg c hc) (Nat.cast_nonneg _))

theorem restrictLabels_primeMass_le : (L.restrictLabels P).primeMass ≤ L.primeMass := by
  exact L.restrictLabels_sum_le P _ (fun c hc =>
    mul_nonneg (L.weight_nonneg c hc) (Nat.cast_nonneg _))

theorem restrictLabels_primeMass_partition :
    L.primeMass = (L.restrictLabels P).primeMass +
      (L.restrictLabels (fun c => ¬P c)).primeMass := by
  exact L.restrictLabels_sum_partition P _

theorem restrictLabels_small_le (Z : ℝ) : (L.restrictLabels P).small Z ≤ L.small Z := by
  exact L.restrictLabels_sum_le P _ (fun c hc =>
    mul_nonneg (L.weight_nonneg c hc) (Nat.cast_nonneg _))

theorem restrictLabels_missing_le (q : ℕ) :
    (L.restrictLabels P).missing q ≤ L.missing q := by
  simp only [missing, sum_filter]
  apply L.restrictLabels_sum_le P
  intro c hc
  have hw : 0 ≤ (L.restrictLabels P).weight c := L.weight_nonneg c hc
  split_ifs <;> positivity

theorem restrictLabels_R2_le (D : ℕ) (Z : ℝ) :
    (L.restrictLabels P).R2 D Z ≤ L.R2 D Z := by
  unfold R2
  apply sum_le_sum
  intro q _
  exact mul_le_mul_of_nonneg_left (L.restrictLabels_missing_le P q) (by positivity)

theorem restrictLabels_fibre_le (e : ℕ) :
    (∑ c ∈ (L.restrictLabels P).labels.filter
      (fun c => (L.restrictLabels P).cofactor c = e), (L.restrictLabels P).weight c) ≤
    ∑ c ∈ L.labels.filter (fun c => L.cofactor c = e), L.weight c := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro c hc
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hc).1).1, (mem_filter.mp hc).2⟩
  · intro c hc _
    exact L.weight_nonneg c (mem_filter.mp hc).1

end Wu2008DoubleSieve.LabelledPhysical.Family
