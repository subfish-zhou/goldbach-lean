import Wu18938Campaign.M1.Confirmed.ReverseCutoff
import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR2ReverseBlock

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real Filter MathlibNt.SieveTheory.SingularSeries
open scoped Classical Topology

theorem reverse_cutoff_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ r : ℕ,
      reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) →
      reboxingR2Reverse N δ Δ V t r ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨B,hB,T0,hT04,h0⟩ := reverse_cutoff_atom m hη hδ
  obtain ⟨T1,_,h1⟩ := scale m hη hδ
  have hU := liuUniversalProduct_pos
  obtain ⟨T2,h2⟩ := eventually_atTop.mp
    (((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (B / (liuUniversalProduct * ε))))
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht r hr
  obtain ⟨hΔ,hL,_,hq,hqN,_⟩ := h1 N (by omega) i Δ V hb
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  let W := convolutionWuWindows N Δ V
  let L := log (N : ℝ)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hatom := h0 N (by omega) heven i Δ V hb s t hs hst ht r hr
  have hsum : reboxingR2Reverse N δ Δ V t r ≤
      (N : ℝ) * (B / L ^ (5 : ℕ)) * boxConvolutionReciprocalMass W *
        ∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r), (1 : ℝ) / p := by
    calc
      _ ≤ ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
          ∑ p ∈ primeWindow N (reboxingAlpha q Δ t j) (reboxingAlpha q Δ t (j + 1)),
            ((N : ℝ) / ((d : ℝ) * p)) * (B / L ^ (5 : ℕ)) := by
        unfold reboxingR2Reverse
        apply sum_le_sum
        intro j hj
        apply sum_le_sum
        intro d hd
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply sum_le_sum
        intro p hp
        have hh := hatom (j + 1) (by omega) (by have := mem_range.mp hj; omega) d hd p
        simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hh
        exact (hh hp).2
      _ = ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
          ∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r),
            ((N : ℝ) / ((d : ℝ) * p)) * (B / L ^ (5 : ℕ)) :=
        (reboxingAlpha_convolution_sum_partition hq0 hΔ N r W _).symm
      _ = _ := by
        unfold boxConvolutionReciprocalMass
        simp only [mul_sum,sum_mul]
        rw [sum_comm]
        apply sum_congr rfl
        intro d _
        apply sum_congr rfl
        intro p _
        ring
  have hZ : reboxingAlpha q Δ t r ≤ N := hr.trans ((show q ^ (1 / s) ≤ q by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hq.le
      ((div_le_iff₀ (by linarith : 0 < s)).mpr (by linarith) : 1 / s ≤ 1)).trans hqN)
  have hp : (∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r),
      (1 : ℝ) / p) ≤ 2 * L :=
    (reboxing_prime_mass_le_harmonic N hZ).trans (by dsimp [L]; linarith)
  have hmass : 0 ≤ boxConvolutionReciprocalMass W := by
    unfold boxConvolutionReciprocalMass
    positivity
  have hθ := hb.theta_reciprocal_lower (by omega) hη hδ
  have hθ0 : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W :=
    (show 0 ≤ 2 * liuUniversalProduct * (N : ℝ) / log N ^ 2 * boxConvolutionReciprocalMass W
      by positivity).trans hθ
  have hpay : B / liuUniversalProduct / L ^ (2 : ℕ) ≤ ε := by
    have hh := (div_le_iff₀ (mul_pos hU he)).mp (h2 N (by omega))
    simp only [Function.comp_apply] at hh
    apply (div_le_iff₀ (by positivity)).mpr
    apply (div_le_iff₀ hU).mpr
    dsimp [L]
    nlinarith
  apply hsum.trans
  calc
    _ ≤ (N : ℝ) * (B / L ^ (5 : ℕ)) * boxConvolutionReciprocalMass W * (2 * L) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (B / liuUniversalProduct / L ^ (2 : ℕ)) *
        (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2 * boxConvolutionReciprocalMass W) := by
      dsimp [L]
      field_simp
    _ ≤ (B / liuUniversalProduct / L ^ (2 : ℕ)) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W :=
      mul_le_mul_of_nonneg_left hθ (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hpay hθ0

theorem raw_modulus_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      reboxingRawPrimeSum false N δ s t (convolutionWuWindows N Δ V) -
        reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let α := η / 10
  have hα : 0 < α := by dsimp [α]; positivity
  have hU := liuUniversalProduct_pos
  have hbudget := box_eventually_log_power_budget 2
    (show 0 < 1 / (2 * ε * liuUniversalProduct * α) by positivity) hα
  obtain ⟨T,hT⟩ := eventually_atTop.mp hbudget
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN heven i Δ V hb s t hs hst ht
  let W := convolutionWuWindows N Δ V
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos hNr
  have hf : reboxingRawPrimeSum false N δ s t W - reboxingRawPrimeSum true N δ s t W ≤
      ((N : ℝ) / (α * (N : ℝ) ^ α)) * boxConvolutionReciprocalMass W := by
    unfold reboxingRawPrimeSum
    simp only [Bool.false_eq_true,if_false,if_true]
    rw [← sum_sub_distrib]
    simp_rw [← mul_sub,primeWindow_modulus_sum_difference]
    unfold boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hsp := hb.support_geometry (by omega) hη hδ hd
    have hz : (N : ℝ) ^ α ≤ wuLocalCutoff N δ d t := by
      calc
        _ = ((N : ℝ) ^ η) ^ (1 / 10 : ℝ) := by
          rw [← rpow_mul (Nat.cast_nonneg N)]
          dsimp [α]
          congr 1
          ring
        _ ≤ ((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / 10 : ℝ) :=
          rpow_le_rpow (by positivity) (hb.remaining d hd) (by norm_num)
        _ ≤ _ := rpow_le_rpow_of_exponent_le hsp.2.2.1.le
          (one_div_le_one_div_of_le (by linarith : 0 < t) ht)
    have hh := reboxing_raw_repeated_fibre_le (w := wuLocalCutoff N δ d s)
      (by omega) heven hsp.1 hsp.2.1 hα hz
    convert mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (convolutionCoeff W d)) using 1
    ring
  have hθ := hb.theta_reciprocal_lower (by omega) hη hδ
  have hmass : 0 ≤ boxConvolutionReciprocalMass W :=
    sum_nonneg (fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d))
  have hpay := hT N (by omega)
  have hcoef : (N : ℝ) / (α * (N : ℝ) ^ α) ≤
      ε * (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2) := by
    calc
      _ ≤ (N : ℝ) / (α * ((1 / (2 * ε * liuUniversalProduct * α)) * log (N : ℝ) ^ 2)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity)
          (mul_le_mul_of_nonneg_left hpay hα.le)
      _ = _ := by field_simp
  exact hf.trans ((mul_le_mul_of_nonneg_right hcoef hmass).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hθ he.le))

end Wu18938Campaign.M1.Confirmed.Rebox
