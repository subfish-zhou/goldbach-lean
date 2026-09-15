import MathlibNt.SieveTheory.LiLiuFouvryG9ReducedWeights

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Finite upper-sieve transport for the actual rectangle. The explicit local
count majorant is an input to this layer, not an assumed distribution theorem. -/
theorem fouvryG9Rectangle_upper_transport (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPN : ∀ p ∈ P, p.Coprime N)
    {Q η z H : ℝ} (hQ : 0 ≤ Q) (hD : 2 ≤ externalInternalLevel Q η)
    (hη : 0 < η) (hηu : η < 1/8) (hcut : ∀ p ∈ P, (p : ℝ) < z) (hH : 0 ≤ H)
    (hr : ∀ d ∈ Icc 1 ⌊Q⌋₊,
      |bilinearDiscrepancy (fouvryG9LongProducts N ρ k) (fouvryG9RectanglePrimeSupport N ρ k)
        (fouvryG9LongAlpha N ρ k) (fouvryG9RectangleBeta N) N d| ≤ H/d.totient) :
    let U := fouvryG9LongProducts N ρ k
    let V := fouvryG9RectanglePrimeSupport N ρ k
    let α := fouvryG9LongAlpha N ρ k
    let β := fouvryG9RectangleBeta N
    let D := externalInternalLevel Q η
    fouvryG9RectangleSifted N ρ k P ≤
      (∑ t ∈ externalTags true P D η z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D η z t d * g9IntegerFibreCenter U V α β d) +
      (∑ t ∈ externalTags true P D η z,
        |signedError U V (Ioc 0 ⌊Q⌋₊) α β (fun d => externalTerm true P D η z t d) N|) +
      ((externalTags true P D η z).card : ℝ)*H*(4/D^(η^2))*(1+Real.log (⌊Q⌋₊ : ℕ))^2 := by
  dsimp only
  let U := fouvryG9LongProducts N ρ k
  let V := fouvryG9RectanglePrimeSupport N ρ k
  let α := fouvryG9LongAlpha N ρ k
  let β := fouvryG9RectangleBeta N
  let D := externalInternalLevel Q η
  let r := bilinearDiscrepancy U V α β N
  let S := externalTags true P D η z
  let f := fun t => ∑ d ∈ Icc 1 ⌊Q⌋₊, externalTerm true P D η z t d*r d
  let p := fun t => ∑ d ∈ (P.prod id).divisors, externalTerm true P D η z t d*r d
  have hlev : D^(1+η+η^9) = Q := externalInternalLevel_level hQ hη hηu
  have hb := externalUpperFamily_full_transport_budget P hP (D := D) z hD hη hηu r H hH
    (by rw [hlev]; exact hr)
  rw [hlev] at hb
  have hprim : (∑ t ∈ S, p t) ≤ (∑ t ∈ S, |f t|)+∑ t ∈ S, |f t-p t| := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro t _
    linarith [le_abs_self (f t), neg_le_abs (f t-p t)]
  have he : (∑ t ∈ S, |f t|) =
      ∑ t ∈ S, |signedError U V (Ioc 0 ⌊Q⌋₊) α β
        (fun d => externalTerm true P D η z t d) N| := by
    apply sum_congr rfl
    intro t _
    congr 1
    exact externalTerm_full_eq_signedError true P D η z t N hPN U V α β Q
  have hu := fouvryG9Rectangle_weighted_upper N ρ k P hP hD hη hηu hcut
  dsimp only at hu
  have hp : (∑ t ∈ S, p t) ≤ (∑ t ∈ S, |f t|)+
      ((S.card : ℝ)*H*(4/D^(η^2))*(1+Real.log (⌊Q⌋₊ : ℕ))^2) :=
    hprim.trans (add_le_add le_rfl hb)
  rw [he] at hp
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
