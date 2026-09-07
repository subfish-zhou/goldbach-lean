import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryCountCenter
import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryPrimorialPairing

open Finset
open scoped BigOperators Classical
open Wu2004MeanValue
open MathlibNt.SieveTheory.LiLiuPrereqWF
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11OrdinaryCenter_eq_density (N : ℕ) (S : Finset ℕ) (L U : ℝ) (d : ℕ) :
    goldbachG11OrdinaryCenter N S L U d =
      ∑ m ∈ S, (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ)*(realPrimeCount U-realPrimeCount L)*progressionDensity m d := by
  apply sum_congr rfl
  intro m _
  change (if m.Coprime d then _ else 0) =
    _*(if d.Coprime m then (d.totient : ℝ)⁻¹ else 0)
  by_cases h : m.Coprime d
  · rw [if_pos h,if_pos h.symm]
    ring
  · have hh : ¬d.Coprime m := fun hc => h hc.symm
    rw [if_neg h,if_neg hh]
    simp

theorem goldbachG11OrdinaryCenter_externalDensity (N : ℕ) (S P : Finset ℕ)
    (L U D θ z : ℝ) :
    (∑ t ∈ externalTags true P D θ z, ∑ d ∈ (P.prod id).divisors,
      externalTerm true P D θ z t d*goldbachG11OrdinaryCenter N S L U d) =
      ∑ m ∈ S, (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ)*(realPrimeCount U-realPrimeCount L)*
        externalDensity true P D θ z (progressionDensity m) := by
  simp only [goldbachG11OrdinaryCenter_eq_density,externalDensity,mul_sum]
  simp_rw [sum_comm (s := (P.prod id).divisors) (t := S)]
  rw [sum_comm (s := externalTags true P D θ z) (t := S)]
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro d _
  ring

/-- The genuine high-band all-prime sieve envelope. Its error is paired only
on squarefree reduced moduli; the main term is the ordinary pi-centered one. -/
theorem goldbachG11OrdinaryGrid_sifted_upper {N : ℕ} {ε ρ Q θ z : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    {k : ℕ × ℕ} (hk : k ∈ goldbachG11GridUsed N ε ρ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPN : ∀ p ∈ P, p.Coprime N)
    (hQ : 1 ≤ Q) (hD : 2 ≤ externalInternalLevel Q θ)
    (hθ : 0 < θ) (hθu : θ < 1/8) (hcut : ∀ p ∈ P, (p : ℝ) < z) :
    goldbachG11AllPrimeSiftedMass N (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k) P ≤
      (∑ m ∈ goldbachG11GridLong N ε ρ k,
        (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
          ((N : ℝ)^(4/33 : ℝ)) m : ℝ)*
        (realPrimeCount (goldbachG11GridProfileHi ρ k)-realPrimeCount (goldbachG11GridProfileLo N ρ k))*
        externalDensity true P (externalInternalLevel Q θ) θ z (progressionDensity m)) +
      Real.exp (8*(θ⁻¹)^3)*
        (∑ d ∈ goldbachG11LinkedModuli N ⌊Q⌋₊,|goldbachG11OrdinaryRectangleResidual N ε ρ k d N|) := by
  let D := externalInternalLevel Q θ
  let S := goldbachG11GridLong N ε ρ k
  let V := goldbachG11GridShort N ρ k
  let C := goldbachG11OrdinaryCenter N S (goldbachG11GridProfileLo N ρ k) (goldbachG11GridProfileHi ρ k)
  let R := fun d => goldbachG11OrdinaryRectangleResidual N ε ρ k d N
  let I := externalTags true P D θ z
  have hu := externalFamily_weighted_sequence_sieve_centered P hP hD hθ hθu hcut
    (S ×ˢ V) (fun v : ℕ × ℕ => ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs)
    (goldbachG11AllPrimeWeight N) (fun v _ => goldbachG11AllPrimeWeight_nonneg N v) C
  have he : (∑ t ∈ I, ∑ d ∈ (P.prod id).divisors,
      externalTerm true P D θ z t d*
        (weightedDivCount (S ×ˢ V) (fun v : ℕ × ℕ => ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs)
          (goldbachG11AllPrimeWeight N) d-C d)) =
      ∑ t ∈ I, ∑ d ∈ (P.prod id).divisors,externalTerm true P D θ z t d*R d := by
    apply sum_congr rfl
    intro t _
    apply sum_congr rfl
    intro d _
    by_cases h : externalTerm true P D θ z t d = 0
    · simp only [h,zero_mul]
    · have hd := (externalTerm_coprime_of_ne_zero true P D θ z t N d hPN h).symm
      rw [goldbachG11OrdinaryGrid_centered_eq hρ hρu hbig hk d hd]
  rw [he] at hu
  have hm := goldbachG11OrdinaryCenter_externalDensity N S P
    (goldbachG11GridProfileLo N ρ k) (goldbachG11GridProfileHi ρ k) D θ z
  rw [hm] at hu
  have hr : (∑ t ∈ I, ∑ d ∈ (P.prod id).divisors,externalTerm true P D θ z t d*R d) ≤
      Real.exp (8*(θ⁻¹)^3)*(∑ d ∈ goldbachG11LinkedModuli N ⌊Q⌋₊,|R d|) := by
    calc
      _ ≤ ∑ _t ∈ I, (∑ d ∈ goldbachG11LinkedModuli N ⌊Q⌋₊,|R d|) := by
        apply sum_le_sum
        intro t ht
        exact (le_abs_self _).trans (goldbachG11_external_primorial_pairing N P hP hPN hQ hD hθ hθu t ht R)
      _ = (I.card : ℝ)*(∑ d ∈ goldbachG11LinkedModuli N ⌊Q⌋₊,|R d|) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (externalTags_card_and_wellFactorable true P z hD hθ hθu).1.le
        (sum_nonneg fun d _ => abs_nonneg _)
  exact hu.trans (add_le_add (le_refl _) hr)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig