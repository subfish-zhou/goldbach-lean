import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernelIntegralBound
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabKernelMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabSieve
import MathlibNt.SieveTheory.LiLiuGoldbachG11NormalizedIntegralEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachG11EulerFactorNormalized
import MathlibNt.SieveTheory.LiLiuGoldbachG11RemainderPayments

open Filter Set LiLiuPrereqBuchstab
open scoped Topology

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- Exact envelope: exponent A=3; the three actual remainders are paid separately.
The coefficient is the uniform level coefficient 8, not the author's low-band weight. -/
theorem goldbachG12NormalizedIntegral_envelope_loss
    (B C τ η ν d W : ℝ) (hB : 0 ≤ B)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hη : 0 < η) (hν : 0 < ν) (hd : 0 < d)
    (hW0 : 0 ≤ W)
    (hW : ∀ u ∈ Icc (3 : ℝ) (1141/132), buchstab u ≤ W) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ _hEven : Even N,
      goldbachG12BuchstabSieveEnvelope N (goldbachG11SieveCutoff B N) 3 C
          (τ * Real.exp Real.eulerMascheroniConstant) η ≤
        (8*(1+τ)^3*(W+η)*(goldbachG12PrimeIntegral (fun _ => 1)+ν)+3*d) *
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨K,hK,hkernel⟩ := goldbachG12PrimeKernel_one_le_integral_eventually ν hν
  obtain ⟨E,_,heuler⟩ := goldbachG11EulerFactor_normalized B τ hB hτ hτ1
  obtain ⟨G,_,hgeom⟩ := goldbachG11SieveParameters_eventually B 2 τ hB hτ hτ1
  obtain ⟨S,_,hsmall⟩ := goldbachG11_smallOutput_paid d hd
  obtain ⟨X,_,hexcess⟩ := goldbachG11_buchstabExcess_paid d hd
  obtain ⟨L,hlogerr⟩ := eventually_atTop.mp (goldbachG11NormalizedIntegral_logError_paid (400*C) d hd)
  obtain ⟨Q,_,hnonneg⟩ := goldbachG12BuchstabUpperMass_eventually_nonneg η hη
  refine ⟨max K (max E (max G (max S (max X (max L Q))))), by omega, ?_⟩
  intro N hN hEven
  have hN4 : 4 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hCpos := (SingularSeries.liuSingularSeries_pos N).le
  have hk := hkernel N (by omega)
  have hm := goldbachG12BuchstabUpperMass_le_primeKernel hN4 η W hη.le hW
  have hmul := mul_le_mul_of_nonneg_left hk (add_nonneg hW0 hη.le)
  have hm' : goldbachG12BuchstabUpperMass N η ≤
      ((W+η)*(goldbachG12PrimeIntegral (fun _ => 1)+ν)) * (N : ℝ) / Real.log (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (hm.trans hmul) (div_pos hNpos hlogpos).le
    field_simp at hh ⊢
    nlinarith only [hh]
  have hmain := mul_le_mul_of_nonneg_left hm'
    (show 0 ≤ 8*(1+τ)^3*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) by positivity)
  have hg := hgeom N (by omega)
  have hs := hsmall N (by omega) (goldbachG11SieveCutoff B N) ((show (0 : ℝ) ≤ max 2 2 by norm_num).trans hg.1) hg.2.1
  have hx := hexcess N (by omega) τ hτ.le hτ1
  have hl := hlogerr N (by omega)
  have hm0 := hnonneg N (by omega)
  have he := mul_le_mul_of_nonneg_left (heuler N (by omega) hEven)
    (show 0 ≤ goldbachG12BuchstabUpperMass N η + 8400*N/(N : ℝ)^(4/53 : ℝ) by positivity)
  unfold goldbachG12BuchstabSieveEnvelope
  calc
    _ ≤ (goldbachG12BuchstabUpperMass N η + 8400*N/(N : ℝ)^(4/53 : ℝ))*
          (8*(1+τ)^3*SingularSeries.liuSingularSeries N/Real.log (N : ℝ)) +
          400*C*N/Real.log (N : ℝ)^(3 : ℝ) + 8000*(Nat.ceil (goldbachG11SieveCutoff B N) : ℝ) := by
      nlinarith only [he]
    _ ≤ _ := by
      have hmain' : goldbachG12BuchstabUpperMass N η *
          (8*(1+τ)^3*SingularSeries.liuSingularSeries N/Real.log (N : ℝ)) ≤
          (8*(1+τ)^3*(W+η)*(goldbachG12PrimeIntegral (fun _ => 1)+ν))*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
        convert hmain using 1 <;> first | rfl | ring
      ring_nf at hmain' hx hl hs ⊢
      linarith only [hmain', hx, hl, hs]

/-- Continuity selects one strictly positive common loss; no free mesh, distribution,
or target-shaped premise is left in the final consumers. -/
theorem goldbachG12NormalizedIntegral_choose_loss (W δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      8*(1+t)^3*(W+t)*(goldbachG12PrimeIntegral (fun _ => 1)+t) <
        8*W*goldbachG12PrimeIntegral (fun _ => 1)+δ := by
  let f : ℝ → ℝ := fun t => 8*(1+t)^3*(W+t)*(goldbachG12PrimeIntegral (fun _ => 1)+t)
  have hc : ContinuousAt f 0 := by dsimp [f]; fun_prop
  obtain ⟨r,hr,hclose⟩ := Metric.continuousAt_iff.mp hc δ hδ
  let t : ℝ := min (r/2) (1/2)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have htr : t < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hf := hclose (show dist t 0 < r by simpa [Real.dist_eq,abs_of_pos ht] using htr)
  have hup := (abs_lt.mp (show |f t - f 0| < δ by simpa [Real.dist_eq] using hf)).2
  refine ⟨t,ht,ht1,?_⟩
  dsimp [f] at hup
  nlinarith only [hup]

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig