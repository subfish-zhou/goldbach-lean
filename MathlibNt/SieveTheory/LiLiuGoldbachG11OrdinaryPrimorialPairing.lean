import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryGridSource
import MathlibNt.SieveTheory.LiLiuFouvryG9WFBridge
import MathlibNt.SieveTheory.LiLiuFouvryG9ReducedWeights

open Finset
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Finite prime carrier: direct Mathlib proof, with no private-name access. -/
theorem goldbachG11_squarefree_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Squarefree (P.prod id) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => ?_) (fun p hp => (hP p hp).squarefree)
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)

/-- Pair the unchanged actual WF member only over primorial divisors. Ordinary
squarefree distribution suffices; no non-squarefree error estimate is claimed. -/
theorem goldbachG11_external_primorial_pairing (N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPN : ∀ p ∈ P, p.Coprime N)
    {Q θ z : ℝ} (hQ : 1 ≤ Q) (hD : 2 ≤ externalInternalLevel Q θ)
    (hθ : 0 < θ) (hθu : θ < 1/8) (t : List ℕ)
    (ht : t ∈ externalTags true P (externalInternalLevel Q θ) θ z) (R : ℕ → ℝ) :
    |∑ d ∈ (P.prod id).divisors,
      externalTerm true P (externalInternalLevel Q θ) θ z t d*R d| ≤
      ∑ d ∈ goldbachG11LinkedModuli N ⌊Q⌋₊, |R d| := by
  let c := fun d => externalTerm true P (externalInternalLevel Q θ) θ z t d
  have hw := externalTerm_signedWellFactorable true P z t (zero_le_one.trans hQ) hD hθ hθu ht
  have hs := hw.factorSupported hQ
  have hprod := goldbachG11_squarefree_prime_product P hP
  have hpoint : ∀ d ∈ (P.prod id).divisors,
      |c d*R d| ≤ if d ∈ goldbachG11LinkedModuli N ⌊Q⌋₊ then |R d| else 0 := by
    intro d hd
    by_cases hc : c d = 0
    · rw [hc,zero_mul,abs_zero]
      split_ifs
      · exact abs_nonneg _
      · exact le_rfl
    · have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd)
        (Nat.pos_of_ne_zero hprod.ne_zero)
      have hdQ : d ≤ ⌊Q⌋₊ := (Nat.le_floor_iff (zero_le_one.trans hQ)).mpr (hs d hc).2
      have hsq : Squarefree d := hprod.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      have hcop := externalTerm_coprime_of_ne_zero true P (externalInternalLevel Q θ) θ z t N d hPN hc
      have hdS : d ∈ goldbachG11LinkedModuli N ⌊Q⌋₊ :=
        mem_filter.mpr ⟨mem_Icc.mpr ⟨hd0,hdQ⟩,hsq,hcop.symm⟩
      have hc1 := hw.1 d
      rw [fouvryTau_order_one (Nat.ne_of_gt hd0),Nat.cast_one] at hc1
      rw [if_pos hdS,abs_mul]
      exact (mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)).trans_eq (one_mul _)
  calc
    _ ≤ ∑ d ∈ (P.prod id).divisors, |c d*R d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (P.prod id).divisors,
        if d ∈ goldbachG11LinkedModuli N ⌊Q⌋₊ then |R d| else 0 := sum_le_sum hpoint
    _ ≤ _ := by
      rw [← sum_filter]
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact (mem_filter.mp hd).2
      · intro d _ _
        exact abs_nonneg _

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig