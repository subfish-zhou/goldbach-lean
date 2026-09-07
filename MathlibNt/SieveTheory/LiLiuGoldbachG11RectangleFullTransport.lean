import MathlibNt.SieveTheory.LiLiuGoldbachG11FouvryFiniteSieve
import MathlibNt.SieveTheory.LiLiuFouvryG9ReducedWeights

open Finset
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Finite transport for the literal G11 rectangle. The arbitrary-modulus
majorant is exposed here and supplied by the actual grid producer downstream. -/
theorem goldbachG11Rectangle_upper_transport (N : ℕ) (U V : Finset ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPN : ∀ p ∈ P, p.Coprime N)
    {Q θ z H : ℝ} (hQ : 0 ≤ Q) (hD : 2 ≤ externalInternalLevel Q θ)
    (hθ : 0 < θ) (hθu : θ < 1/8) (hcut : ∀ p ∈ P, (p : ℝ) < z) (hH : 0 ≤ H)
    (hr : ∀ d ∈ Icc 1 ⌊Q⌋₊,
      |bilinearDiscrepancy U V
        (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
          ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
        (fun p => if p.Coprime N then primeSWBeta p else 0) N d| ≤ H/d.totient) :
    let D := externalInternalLevel Q θ
    let α := fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) m : ℝ)
    let β := fun p => if p.Coprime N then primeSWBeta p else 0
    goldbachG11RectangleSiftedMass N U V P ≤
      (∑ m ∈ U, ∑ p ∈ V, goldbachG11RectangleWeight N (m,p)*
        externalDensity true P D θ z (progressionDensity (m*p))) +
      (∑ t ∈ externalTags true P D θ z,
        |signedError U V (Ioc 0 ⌊Q⌋₊) α β (fun d => externalTerm true P D θ z t d) N|) +
      ((externalTags true P D θ z).card : ℝ)*H*(4/D^(θ^2))*(1+Real.log (⌊Q⌋₊ : ℕ))^2 := by
  dsimp only
  let α := fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ)) m : ℝ)
  let β := fun p => if p.Coprime N then primeSWBeta p else 0
  let D := externalInternalLevel Q θ
  let r := bilinearDiscrepancy U V α β N
  let S := externalTags true P D θ z
  let f := fun t => ∑ d ∈ Icc 1 ⌊Q⌋₊, externalTerm true P D θ z t d*r d
  let p := fun t => ∑ d ∈ (P.prod id).divisors, externalTerm true P D θ z t d*r d
  have hlev : D^(1+θ+θ^9) = Q := externalInternalLevel_level hQ hθ hθu
  have hb := externalUpperFamily_full_transport_budget P hP (D := D) z hD hθ hθu r H hH
    (by rw [hlev]; exact hr)
  rw [hlev] at hb
  have hprim : (∑ t ∈ S, p t) ≤ (∑ t ∈ S, |f t|)+∑ t ∈ S, |f t-p t| := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro t _
    linarith [le_abs_self (f t),neg_le_abs (f t-p t)]
  have he : (∑ t ∈ S, |f t|) =
      ∑ t ∈ S, |signedError U V (Ioc 0 ⌊Q⌋₊) α β
        (fun d => externalTerm true P D θ z t d) N| := by
    apply sum_congr rfl
    intro t _
    congr 1
    exact externalTerm_full_eq_signedError true P D θ z t N hPN U V α β Q
  have hu := goldbachG11RectangleSiftedMass_external_upper N U V P hP hD hθ hθu hcut
  dsimp only at hu
  have hp : (∑ t ∈ S, p t) ≤ (∑ t ∈ S, |f t|)+
      ((S.card : ℝ)*H*(4/D^(θ^2))*(1+Real.log (⌊Q⌋₊ : ℕ))^2) :=
    hprim.trans (add_le_add le_rfl hb)
  rw [he] at hp
  dsimp only [S,p,r,α,β,D,goldbachG11RectangleWeight] at hp ⊢
  linarith only [hu,hp]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig