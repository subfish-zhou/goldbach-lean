import HighO3Geometry
import HighCrossFinite
import MathlibNt.Wu2008DoubleSieve.Omega3Relative
import MathlibNt.Wu2008DoubleSieve.OmegaRepeated

namespace HighO3
open Finset Real Wu2008DoubleSieve HighBoxRecovery HighTheta Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries
noncomputable section

/-- Every fixed positive power saving is paid on the actual Theta, uniformly
in all finite prime windows satisfying the total-product gap. -/
theorem power_payment {δ η ε C r : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η)
    (hε : 0 < ε) (hC : 0 < C) (hr : 0 < r) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ (i : ℕ) (W : Fin i → Finset ℕ),
      (∀ j p, p ∈ W j → p.Prime) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      (C*((N : ℝ)/(N : ℝ)^r))*boxConvolutionReciprocalMass W ≤
        ε*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  have hU := liuUniversalProduct_pos
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget 2
      (show 0 < C/(2*ε*liuUniversalProduct) by positivity) hr)
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN i W hW hsize
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hpay := hT N ((le_max_right _ _).trans hN)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcoef : C*((N : ℝ)/(N : ℝ)^r) ≤ ε*(2*liuUniversalProduct*N/log N^2) := by
    calc
      _ ≤ C*((N : ℝ)/((C/(2*ε*liuUniversalProduct))*log N^2)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity) hpay) hC.le
      _ = _ := by field_simp
  have hmass : 0 ≤ boxConvolutionReciprocalMass W :=
    sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  calc
    _ ≤ (ε*(2*liuUniversalProduct*N/log N^2))*boxConvolutionReciprocalMass W :=
      mul_le_mul_of_nonneg_right hcoef hmass
    _ = ε*((2*liuUniversalProduct*N/log N^2)*boxConvolutionReciprocalMass W) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (theta_from_actual_support W hN4 hδ hη hW hsize) hε.le

/-- Exceptional-output union keeps all ordered triples and all convolution weights. -/
theorem exceptional_mass {i N : ℕ} {δ η s t : ℝ} (W : Fin i → Finset ℕ)
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hw : ∀ d ∈ boxConvolutionSupport W, 0 < d ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    omega3ExceptionalOutputCount N δ s t W ≤
      (4*(1/η)^3*((N : ℝ)/(N : ℝ)^δ))*boxConvolutionReciprocalMass W := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmass : (∑ d ∈ boxConvolutionSupport W,(convolutionCoeff W d : ℝ)) ≤
      (N : ℝ)^(1/2-δ)*boxConvolutionReciprocalMass W := by
    unfold boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (hw d hd).1
    have hQ : (d : ℝ) ≤ (N : ℝ)^(1/2-δ) := (hw d hd).2.trans
      (rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith))
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hd0).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg (convolutionCoeff W d))
  have hrec : 0 ≤ boxConvolutionReciprocalMass W :=
    sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  have hpow : sqrt (N : ℝ)*(N : ℝ)^(1/2-δ) = (N : ℝ)/(N : ℝ)^δ := by
    rw [sqrt_eq_rpow,← rpow_add hNr]
    calc
      _ = (N : ℝ)^(1-δ) := by congr 1; ring
      _ = _ := by rw [rpow_sub hNr,rpow_one]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W,(convolutionCoeff W d : ℝ)*
        ((1/η)^3*((omega3ExceptionalOutputs N δ).card : ℝ)) :=
      omega3_exceptional_count_le W hN he hη (fun d hd =>
        (support_bounds (by omega) (hw d hd).1 hδ hδhi hη (hw d hd).2 hs hst ht).2.2.2.2.1)
    _ = ((1/η)^3*((omega3ExceptionalOutputs N δ).card : ℝ))*
        ∑ d ∈ boxConvolutionSupport W,(convolutionCoeff W d : ℝ) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ ((1/η)^3*(4*sqrt (N : ℝ)))*
        ((N : ℝ)^(1/2-δ)*boxConvolutionReciprocalMass W) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (omega3ExceptionalOutputs_card_le (by omega) hδ.le) (by positivity))
        hmass (sum_nonneg fun d _ => Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← hpow]; ring

/-- Actual repeated-d prime term, not the separate X-majorant repeated-p1 term. -/
theorem repeated_mass {i N : ℕ} {δ η s t : ℝ} (W : Fin i → Finset ℕ)
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hw : ∀ d ∈ boxConvolutionSupport W, 0 < d ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    wuOmegaRepeatedSum N δ s t W ≤
      ((1/η)*((N : ℝ)/(N : ℝ)^η))*boxConvolutionReciprocalMass W := by
  unfold wuOmegaRepeatedSum boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  have hg := support_bounds (by omega) (hw d hd).1 hδ hδhi hη (hw d hd).2 hs hst ht
  have hf := omega_repeated_fibre_le (M := d*N)
    (v := wuLocalCutoff N δ d t) (w := wuLocalCutoff N δ d s)
    hN he hg.1 hg.2.1 hη hg.2.2.2.2.1
  have hm := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg (convolutionCoeff W d) : (0 : ℝ) ≤ _)
  unfold wuOmegaRepeated
  convert hm using 1
  ring

/-- All THREE genuine counts are paid separately, then summed, before N and
all moving windows. No target-mass or analytic-payment premise. -/
theorem losses_paid {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (W : Fin i → Finset ℕ),
      (∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^η ≤ p) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      HighCross.switchingLoss N δ s t W ≤ ε*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  have heps : 0 < ε/3 := by positivity
  obtain ⟨T1,hT14,hB⟩ := power_payment hδ.le hη heps (show 0 < (1/η)^4 by positivity) hη
  obtain ⟨T2,_,hE⟩ := power_payment hδ.le hη heps (show 0 < 4*(1/η)^3 by positivity) hδ
  obtain ⟨T3,_,hP⟩ := power_payment hδ.le hη heps (show 0 < 1/η by positivity) hη
  refine ⟨max T1 (max T2 T3),hT14.trans (le_max_left _ _),?_⟩
  intro N hN he i W hW hsize s t hs hst ht
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 T3).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 T3).trans ((le_max_right T1 _).trans hN)
  have hN4 := hT14.trans hN1
  have hw : ∀ d ∈ boxConvolutionSupport W, 0 < d ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η) :=
    fun d hd => ⟨boxConvolutionSupport_pos (fun j p hp => (hW j p hp).1.pos) hd,hsize d hd⟩
  have hg := fun d hd => support_bounds (show 2 ≤ N by omega) (hw d hd).1 hδ hδhi hη (hw d hd).2 hs hst ht
  have hb := omega3_badDCount_le_reciprocal_mass (s := s) W hN4 he hη
    (fun d hd => ⟨(hg d hd).1,(hg d hd).2.1⟩)
    (fun d hd => (hg d hd).2.2.2.2.1) (by
      intro d hd q hq
      have hp := Nat.mem_primeFactors.mp hq
      exact omega3_support_prime_lower W hW hd hp.1 hp.2.1)
  have hexc := exceptional_mass W hN4 he hδ hδhi hη hw hs hst ht
  have hr := repeated_mass W hN4 he hδ hδhi hη hw hs hst ht
  have hbpay := hb.trans (hB N hN1 i W (fun j p hp => (hW j p hp).1) hsize)
  have hepay := hexc.trans (hE N hN2 i W (fun j p hp => (hW j p hp).1) hsize)
  have hrpay := hr.trans (hP N hN3 i W (fun j p hp => (hW j p hp).1) hsize)
  unfold HighCross.switchingLoss
  linarith

end
end HighO3
