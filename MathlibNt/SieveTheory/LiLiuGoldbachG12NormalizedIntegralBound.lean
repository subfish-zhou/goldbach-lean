import MathlibNt.SieveTheory.LiLiuGoldbachG12NormalizedIntegralEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabMajorant

open Set LiLiuPrereqBuchstab
open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- The loss is selected before all later sieve constants. It is not an assumption
on the target bound; all analytic error terms are absorbed for every fixed B,C. -/
theorem goldbachG12NormalizedIntegral_envelope (W δ : ℝ) (hW0 : 0 ≤ W) (hδ : 0 < δ)
    (hW : ∀ u ∈ Icc (3 : ℝ) (1141/132), buchstab u ≤ W) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∀ B C : ℝ, 0 ≤ B →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ _hEven : Even N,
        goldbachG12BuchstabSieveEnvelope N (goldbachG11SieveCutoff B N) 3 C
            (τ * Real.exp Real.eulerMascheroniConstant) τ ≤
          (8*W*goldbachG12PrimeIntegral (fun _ => 1)+δ) *
            (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨τ,hτ,hτ1,hcoeff⟩ := goldbachG12NormalizedIntegral_choose_loss W (δ/2) (by positivity)
  refine ⟨τ,hτ,hτ1,?_⟩
  intro B C hB
  obtain ⟨N₀,hN₀,hbound⟩ := goldbachG12NormalizedIntegral_envelope_loss
    B C τ τ τ (δ/6) W hB hτ hτ1 hτ hτ (by positivity) hW0 hW
  refine ⟨N₀,hN₀,?_⟩
  intro N hN hEven
  have hM : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg _)) (sq_nonneg _)
  exact (hbound N hN hEven).trans
    (mul_le_mul_of_nonneg_right (by linarith only [hcoeff]) hM)

/-- Actual original-cross output upper bound, with its complete sieve error paid. -/
theorem goldbachG12OutputTotal_le_normalizedIntegral (W δ : ℝ) (hW0 : 0 ≤ W) (hδ : 0 < δ)
    (hW : ∀ u ∈ Icc (3 : ℝ) (1141/132), buchstab u ≤ W) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε : ℝ),
      (400 * ∑ m ∈ goldbachG12ActiveProductSupport N,
        goldbachG12NormalizedCoefficient N m *
          ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card : ℝ)) ≤
        (8*W*goldbachG12PrimeIntegral (fun _ => 1)+δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨τ,hτ,_,henv⟩ := goldbachG12NormalizedIntegral_envelope W δ hW0 hδ hW
  obtain ⟨B,C,hB,_,K,hK,hactual⟩ := goldbachG12OutputTotal_le_concreteBuchstabSieve
    3 (τ*Real.exp Real.eulerMascheroniConstant) τ (by norm_num) (by positivity) hτ
  obtain ⟨L,_,hbound⟩ := henv B C hB.le
  refine ⟨max K L,by omega,?_⟩
  intro N hN hEven ε
  exact (hactual N (by omega) hEven ε).trans (hbound N (by omega) hEven)

/-- Unconditional uniform-level bound, using the certified unbounded Buchstab majorant.
This is not the author's low/high weighted coefficient. -/
theorem goldbachG12OutputTotal_le_uniformIntegral (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε : ℝ),
      (400 * ∑ m ∈ goldbachG12ActiveProductSupport N,
        goldbachG12NormalizedCoefficient N m *
          ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card : ℝ)) ≤
        (8*(564383/1000000 : ℝ)*goldbachG12PrimeIntegral (fun _ => 1)+δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) :=
  goldbachG12OutputTotal_le_normalizedIntegral _ δ (by norm_num) hδ
    (fun _ hu => LiLiuGoldbachG12BuchstabMajorant.buchstab_le_564383 hu.1)

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
