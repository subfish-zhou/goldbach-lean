import MathlibNt.SieveTheory.LiLiuGoldbachG12RosserFactor
import MathlibNt.SieveTheory.LiLiuGoldbachG12CommonMass

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
open scoped BigOperators
noncomputable section

theorem goldbachG12LinkedBoundingSieve_rem_eq_common (N : ℕ) (hEven : Even N) (ε Z : ℝ)
    {d : ℕ} (hd : d ∣ goldbachB10ProdPrimes N Z) :
    (goldbachG12LinkedBoundingSieve N hEven ε Z (goldbachG12PrimeWindowMainMass N ε)).rem d =
      goldbachG12CommonDivisorResidual N ε d :=
  goldbachG12LinkedBoundingSieve_rem N hEven ε Z (goldbachG12PrimeWindowMainMass N ε) hd

/-- True Rosser divisors embed into the proved squarefree coprime carrier,
including d=1. No full-modulus removal of the squarefree condition is used. -/
theorem goldbachG12Linked_upperErrSum_le (N : ℕ) (hEven : Even N) (ε Z : ℝ)
    (D Q : ℕ) (hDQ : D ≤ Q+1) :
    let S := goldbachG12LinkedBoundingSieve N hEven ε Z (goldbachG12PrimeWindowMainMass N ε)
    let P := goldbachB10ProdPrimes N Z
    LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight P D) ≤
      ∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG12CommonDivisorResidual N ε d| := by
  classical
  let S := goldbachG12LinkedBoundingSieve N hEven ε Z (goldbachG12PrimeWindowMainMass N ε)
  let P := goldbachB10ProdPrimes N Z
  have hsub : (P.divisors.filter (fun d => d < D)) ⊆ goldbachG11LinkedModuli N Q := by
    intro d hd
    obtain ⟨hdP, hdD⟩ := mem_filter.mp hd
    have hdvd := (Nat.mem_divisors.mp hdP).1
    have hdsq := Squarefree.squarefree_of_dvd hdvd (goldbachB10ProdPrimes_squarefree N Z)
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hdsq.ne_zero
    have hdQ : d ≤ Q := by omega
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hd1, hdQ⟩, hdsq,
      (goldbachB10_dvd_prodPrimes_coprime_N hdvd).symm⟩
  change (∑ d ∈ P.divisors.filter (fun d => d < D),
    |LinearSieve.upperRosserWeight P D d| * |S.rem d|) ≤ _
  calc
    _ ≤ ∑ d ∈ P.divisors.filter (fun d => d < D),
        |goldbachG12CommonDivisorResidual N ε d| := by
      apply sum_le_sum
      intro d hd
      have hdvd := (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
      have hr := goldbachG12LinkedBoundingSieve_rem_eq_common N hEven ε Z hdvd
      change |LinearSieve.upperRosserWeight P D d| * |S.rem d| ≤ _
      rw [hr]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (LinearSieve.abs_upperRosserWeight_le_one P D d)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => abs_nonneg _)

/-- The original G12 physical output fibres with their genuine common prime-window mass,
proved Rosser factor and paid distribution error. Main-mass normalization and
small-output asymptotic absorption are deliberately not claimed here. -/
theorem goldbachG12OutputTotal_le_paidRosser (A ρ : ℝ) (hA : 0 < A) (hρ : 0 < ρ) :
    ∃ B C z₀ : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (hEven : Even N) (ε Z Δ s : ℝ),
      z₀ ≤ Z → 2 ≤ Z → 0 < Δ → s = Real.log Δ/Real.log Z →
      3/2 ≤ s → s ≤ 4 → Δ ≤ Real.sqrt N / Real.log (N : ℝ)^B →
      let X := goldbachG12PrimeWindowMainMass N ε
      let S := goldbachG12LinkedBoundingSieve N hEven ε Z X
      (400 * ∑ m ∈ goldbachG12ActiveProductSupport N,
        goldbachG12NormalizedCoefficient N m *
          ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card : ℝ)) ≤
        400*X*(jurkatRichertUpperLinearSieveFactor s+ρ)*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          400*C*N/Real.log (N : ℝ)^A + 8000*(Nat.ceil Z : ℝ) := by
  obtain ⟨B, C, hB, hC, N₀, hN₀, hdist⟩ := goldbachG12CommonDivisorResidual_log_saving A hA
  obtain ⟨z₀, hupper⟩ := goldbachG12LinkedSiftedMass_le_rosserFactor ρ hρ
  refine ⟨B, C, z₀, hB, hC, N₀, hN₀, ?_⟩
  intro N hN hEven ε Z Δ s hz hZ hΔ hs hslo hshi hlevel
  let X := goldbachG12PrimeWindowMainMass N ε
  let S := goldbachG12LinkedBoundingSieve N hEven ε Z X
  let P := goldbachB10ProdPrimes N Z
  let D := Nat.floor Δ+1
  have hN2 : 2 ≤ N := by omega
  have hQ : (Nat.floor Δ : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ)^B :=
    (Nat.floor_le hΔ.le).trans hlevel
  have he : LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight P D) ≤
      C*N/Real.log (N : ℝ)^A :=
    (goldbachG12Linked_upperErrSum_le N hEven ε Z D (Nat.floor Δ) (le_refl _)).trans
      (hdist N hN ε (Nat.floor Δ) hQ)
  have hu := hupper N hEven ε Z Δ s X hz hZ hΔ hs hslo hshi
    (goldbachG12PrimeWindowMainMass_nonneg N ε)
  change goldbachG12LinkedSiftedMass N ε Z ≤
    X*(jurkatRichertUpperLinearSieveFactor s+ρ)*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
      LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight P D) at hu
  have hg := goldbachG12OutputTotal_le_linkedSifted hN2 ε Z
  change (400 * ∑ m ∈ goldbachG12ActiveProductSupport N,
    goldbachG12NormalizedCoefficient N m *
      ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card : ℝ)) ≤
    400*X*(jurkatRichertUpperLinearSieveFactor s+ρ)*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
      400*C*N/Real.log (N : ℝ)^A + 8000*(Nat.ceil Z : ℝ)
  have hadd := hu.trans (add_le_add_right he
    (X*(jurkatRichertUpperLinearSieveFactor s+ρ)*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S))
  have hscaled := mul_le_mul_of_nonneg_left hadd (by norm_num : (0 : ℝ) ≤ 400)
  have hfinal := hg.trans (add_le_add_left hscaled (8000*(Nat.ceil Z : ℝ)))
  convert hfinal using 1 <;> first | rfl | ring

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig