import MathlibNt.Wu2008DoubleSieve.ConvolutionMultiplicity

/-!
# Finite multiplicities for the Omega3 switching

Wu04 (5.3)--(5.4) retains the ordered convolution labels and the increasing
selected triple. We bound a larger Cartesian carrier, never the unweighted
image of its outputs. Repeated prime factors and depth zero are allowed.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

/-- Any finite labelled family of `r` selected large prime divisors has the
Cartesian bound, with arbitrary extra ordering or window restrictions. -/
theorem omega3_prime_labels_card_le {L : Type*} {r N m : ℕ} {η : ℝ}
    (S : Finset L) (t : L → Fin r → ℕ)
    (hinj : Set.InjOn t S)
    (hN : 1 < N) (hm : 0 < m) (hmN : m ≤ N) (hη : 0 < η)
    (ht : ∀ a ∈ S, ∀ j, (t a j).Prime ∧ t a j ∣ m ∧
      (N : ℝ) ^ η ≤ (t a j : ℝ)) :
    (S.card : ℝ) ≤ (1 / η) ^ r := by
  let P := largePrimeDivisors m ((N : ℝ) ^ η)
  have hc : S.card ≤ (Fintype.piFinset (fun _ : Fin r => P)).card := by
    apply card_le_card_of_injOn t _ hinj
    intro a ha
    apply Fintype.mem_piFinset.mpr
    intro j
    obtain ⟨hp, hd, hl⟩ := ht a ha j
    exact mem_largePrimeDivisors.mpr ⟨hp, hd, Nat.ne_of_gt hm, hl⟩
  calc
    (S.card : ℝ) ≤ ((Fintype.piFinset (fun _ : Fin r => P)).card : ℝ) := by
      exact_mod_cast hc
    _ = (P.card : ℝ) ^ r := by simp
    _ ≤ (1 / η) ^ r := pow_le_pow_left₀ (Nat.cast_nonneg _)
      (largePrimeDivisors_card_le_inv hN hm hmN hη) r

/-- Output-fibre counting, not image counting: each output carries every
selected-prime label that reconstructs it. -/
theorem omega3_labels_card_le_outputs {L : Type*} {r N : ℕ} {η : ℝ}
    (S : Finset L) (out : L → ℕ) (t : L → Fin r → ℕ) (E : Finset ℕ)
    (hinj : Set.InjOn (fun a => (out a, t a)) S)
    (hE : ∀ a ∈ S, out a ∈ E)
    (hN : 1 < N) (hη : 0 < η)
    (hm : ∀ a ∈ S, 0 < out a ∧ out a ≤ N)
    (ht : ∀ a ∈ S, ∀ j, (t a j).Prime ∧ t a j ∣ out a ∧
      (N : ℝ) ^ η ≤ (t a j : ℝ)) :
    (S.card : ℝ) ≤ (1 / η) ^ r * (E.card : ℝ) := by
  have heq : ∑ b ∈ E, (S.filter (fun a => out a = b)).card = S.card := by
    rw [sum_card_fiberwise_eq_card_filter]
    congr 1
    exact filter_eq_self.mpr hE
  rw [← heq, Nat.cast_sum]
  calc
    ∑ b ∈ E, ((S.filter (fun a => out a = b)).card : ℝ) ≤
        ∑ _b ∈ E, (1 / η) ^ r := by
      apply sum_le_sum
      intro b _
      by_cases h : (S.filter (fun a => out a = b)).Nonempty
      · obtain ⟨a, ha⟩ := h
        obtain ⟨haS, hab⟩ := mem_filter.mp ha
        refine omega3_prime_labels_card_le _ t ?_ hN
          (hab ▸ (hm a haS).1) (hab ▸ (hm a haS).2) hη ?_
        · intro a ha c hc htc
          exact hinj (mem_filter.mp ha).1 (mem_filter.mp hc).1
            (Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hc).2.symm) htc)
        · intro c hc j
          obtain ⟨hcS, hcb⟩ := mem_filter.mp hc
          simpa only [← hcb] using ht c hcS j
      · rw [not_nonempty_iff_eq_empty.mp h, card_empty, Nat.cast_zero]
        positivity
    _ = (1 / η) ^ r * (E.card : ℝ) := by simp [mul_comm]

/-- A weighted cofactor fibre. Its labels retain `d` and both selected primes;
any other fields (notably the quotient) must be recoverable from these within
the fixed cofactor. The convolution coefficient counts all ordered tuples. -/
theorem omega3_cofactor_weighted_fibre_le
    {L : Type*} {i k N e : ℕ} {η : ℝ}
    (W : Fin i → Finset ℕ) (S : Finset L) (d : L → ℕ) (t : L → Fin 2 → ℕ)
    (hik : i ≤ k) (hN : 1 < N) (he : 0 < e) (heN : e ≤ N) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ) ^ η ≤ (p : ℝ))
    (hinj : Set.InjOn (fun a => (d a, t a)) S)
    (hd : ∀ a ∈ S, d a ∣ e)
    (ht : ∀ a ∈ S, ∀ j, (t a j).Prime ∧ t a j ∣ e ∧
      (N : ℝ) ^ η ≤ (t a j : ℝ)) :
    (∑ a ∈ S, (convolutionCoeff W (d a) : ℝ)) ≤
      (max 1 (1 / η)) ^ (k + 2) := by
  let P := largePrimeDivisors e ((N : ℝ) ^ η)
  let T := e.divisors ×ˢ Fintype.piFinset (fun _ : Fin 2 => P)
  let f := fun a => (d a, t a)
  have hsub : S.image f ⊆ T := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    apply mem_product.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨hd a ha, Nat.ne_of_gt he⟩, ?_⟩
    apply Fintype.mem_piFinset.mpr
    intro j
    obtain ⟨hp, hd, hl⟩ := ht a ha j
    exact mem_largePrimeDivisors.mpr ⟨hp, hd, Nat.ne_of_gt he, hl⟩
  have hsum : (∑ a ∈ S, (convolutionCoeff W (d a) : ℝ)) ≤
      (∑ b ∈ e.divisors, (convolutionCoeff W b : ℝ)) * (P.card : ℝ) ^ 2 := by
    calc
      _ = ∑ b ∈ S.image f, (convolutionCoeff W b.1 : ℝ) := by
        rw [sum_image hinj]
      _ ≤ ∑ b ∈ T, (convolutionCoeff W b.1 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
      _ = _ := by simp [T, sum_product, mul_comm, mul_sum]
  have hmass : (∑ b ∈ e.divisors, (convolutionCoeff W b : ℝ)) ≤
      (max 1 (1 / η)) ^ k := by
    simpa only [Nat.cast_sum] using
      convolutionCoeff_divisor_mass_le_depth W hik hN he heN hη hW
  have hpc : (P.card : ℝ) ≤ max 1 (1 / η) :=
    (largePrimeDivisors_card_le_inv hN he heN hη).trans (le_max_right _ _)
  calc
    _ ≤ (∑ b ∈ e.divisors, (convolutionCoeff W b : ℝ)) * (P.card : ℝ) ^ 2 := hsum
    _ ≤ (max 1 (1 / η)) ^ k * (max 1 (1 / η)) ^ 2 :=
      mul_le_mul hmass (pow_le_pow_left₀ (Nat.cast_nonneg _) hpc 2)
        (sq_nonneg _) (by positivity)
    _ = _ := (pow_add _ _ _).symm

end Wu2008DoubleSieve
