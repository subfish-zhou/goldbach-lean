import MathlibNt.SieveTheory.LiLiuFouvryG9ExternalExceptional
import MathlibNt.SieveTheory.LiLiuFouvryG9RectangleSieve

noncomputable section
open Finset
namespace MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The actual full-integer coefficients have only primes from the original carrier. -/
theorem externalTerm_primeSupported (upper : Bool) (P : Finset ℕ) (D η z : ℝ)
    (t : List ℕ) : PrimeSupported P (externalTerm upper P D η z t) := by
  unfold externalTerm
  split_ifs
  · exact signedFamilyTerm_primeSupported upper P D η t
  · exact primeSupported_mono (signedFamilyTerm_primeSupported true _ D η t)
      (filter_subset _ _)
  · intro n hn
    simp at hn

/-- Non-squarefree coefficients are kept; prime support alone eliminates
non-reduced moduli when the sieve primes are coprime to the actual N. -/
theorem externalTerm_coprime_of_ne_zero (upper : Bool) (P : Finset ℕ) (D η z : ℝ)
    (t : List ℕ) (N d : ℕ) (hPN : ∀ p ∈ P, p.Coprime N)
    (hd : externalTerm upper P D η z t d ≠ 0) : d.Coprime N := by
  have hd0 : d ≠ 0 := by intro h; subst d; simp at hd
  apply Nat.coprime_of_dvd
  intro p hp hpd
  have hpP := externalTerm_primeSupported upper P D η z t d hd
    (Nat.mem_primeFactors.mpr ⟨hp,hpd,hd0⟩)
  exact hp.coprime_iff_not_dvd.mp (hPN p hpP)

/-- Exact reduction of the modulus carrier for the SAME actual external weight. -/
theorem externalTerm_sum_eq_reduced (upper : Bool) (P : Finset ℕ) (D η z : ℝ)
    (t : List ℕ) (N : ℕ) (hPN : ∀ p ∈ P, p.Coprime N)
    (Q : Finset ℕ) (r : ℕ → ℝ) :
    (∑ d ∈ Q, externalTerm upper P D η z t d*r d) =
      ∑ d ∈ reducedModuli Q N, externalTerm upper P D η z t d*r d := by
  unfold reducedModuli
  rw [sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases h : Int.gcd (N : ℤ) d = 1
  · simp [h]
  · have hz : externalTerm upper P D η z t d = 0 := by
      by_contra hd
      have hc := externalTerm_coprime_of_ne_zero upper P D η z t N d hPN hd
      exact h (by simpa using hc.symm.gcd_eq_one)
    simp [hz]

/-- Full interval and reduced C2 error agree without a weight mask. -/
theorem externalTerm_full_eq_signedError (upper : Bool) (P : Finset ℕ) (D η z : ℝ)
    (t : List ℕ) (N : ℕ) (hPN : ∀ p ∈ P, p.Coprime N)
    (U V : Finset ℕ) (α β : ℕ → ℝ) (Q : ℝ) :
    (∑ d ∈ Icc 1 ⌊Q⌋₊, externalTerm upper P D η z t d *
      bilinearDiscrepancy U V α β N d) =
      signedError U V (Ioc 0 ⌊Q⌋₊) α β (fun d => externalTerm upper P D η z t d) N := by
  have hi : Icc 1 ⌊Q⌋₊ = Ioc 0 ⌊Q⌋₊ := by
    ext d
    simp only [mem_Icc,mem_Ioc]
    omega
  rw [hi, externalTerm_sum_eq_reduced upper P D η z t N hPN]
  rfl

end MathlibNt.SieveTheory.LiLiuPrereqWF
