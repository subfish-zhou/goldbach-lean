import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureBuchstab
import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralKernel

/-! # The literal no-gate band integrals and their all-phi envelopes -/

namespace Wu2008DoubleSieve

open Real Set MeasureTheory LiLiuPrereqBuchstab
open scoped Interval

noncomputable def fourthRowTripleNoGateLower (eleven : Bool) : ℝ := if eleven then 25 / 89 else 25 / 103

noncomputable def fourthRowTripleNoGateUpper (eleven : Bool) : ℝ := if eleven then 100 / 291 else 25 / 89

noncomputable def fourthRowTripleNoGateMiddle (f : ℝ → ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (100 / 291 : ℝ)..(2 / 5), primeOrderedInnerIntegral (2 / 5) f t u / u

noncomputable def fourthRowTripleNoGateIntegral (eleven : Bool) (φ : ℝ) : ℝ :=
  ∫ t in fourthRowTripleNoGateLower eleven..fourthRowTripleNoGateUpper eleven,
    ∫ u in (100 / 291 : ℝ)..(2 / 5),
      ∫ v in u..(2 / 5), buchstab ((φ - t - u - v) / u) / (t * u ^ 2 * v)

noncomputable def fourthRowTripleNoGateEnvelope (eleven : Bool) : ℝ :=
  sSup (fourthRowTripleNoGateIntegral eleven '' Ici 2)

theorem fourthRowTripleNoGate_endpoints (eleven : Bool) :
    1 / 10 ≤ fourthRowTripleNoGateLower eleven ∧
      fourthRowTripleNoGateLower eleven ≤ fourthRowTripleNoGateUpper eleven ∧
      fourthRowTripleNoGateUpper eleven ≤ 1 / 2 := by
  cases eleven <;> norm_num [fourthRowTripleNoGateLower, fourthRowTripleNoGateUpper]

theorem fourthRowTripleNoGate_middle_regular {f : ℝ → ℝ → ℝ → ℝ} {M K : ℝ}
    (hw : PrimeOrderedWeight M K f) (hM : 0 ≤ M) (hK : 0 ≤ K) :
    (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |fourthRowTripleNoGateMiddle f t| ≤ 16 * M) ∧
    (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ t' ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |fourthRowTripleNoGateMiddle f t - fourthRowTripleNoGateMiddle f t'| ≤
        16 * K * |t - t'|) := by
  obtain ⟨hb, ht, hu⟩ := primeOrdered_inner_regular hw hM hK
    (by norm_num : (2 / 5 : ℝ) ∈ Icc (1 / 10) (1 / 2))
  have hc (t : ℝ) (hm : t ∈ Icc (1 / 10 : ℝ) (1 / 2)) :=
    primeOrdered_continuous_of_lipschitz (hu t hm)
  refine ⟨fun t hm => ?_, fun t hm t' hm' => ?_⟩
  · exact (primeOrdered_integral_norm_le_four (by norm_num) (by norm_num)
      (by positivity : 0 ≤ 4 * M) (hb t hm)).trans_eq (by ring)
  · have h := primeOrdered_integral_sub_bound (hc t hm) (hc t' hm')
      (by norm_num : (100 / 291 : ℝ) ∈ Icc (1 / 10) (1 / 2))
      (by norm_num : (2 / 5 : ℝ) ∈ Icc (1 / 10) (1 / 2))
      (by positivity : 0 ≤ 4 * K * |t - t'|) (fun u hu' => ht t hm t' hm' u hu')
    exact h.trans_eq (by ring)

theorem fourthRowTripleNoGate_integral_eq (eleven : Bool) (φ : ℝ) :
    fourthRowTripleNoGateIntegral eleven φ =
      ∫ t in fourthRowTripleNoGateLower eleven..fourthRowTripleNoGateUpper eleven,
        fourthRowTripleNoGateMiddle (primeOrderedBuchstabWeight φ) t / t := by
  unfold fourthRowTripleNoGateIntegral fourthRowTripleNoGateMiddle
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u _
  unfold primeOrderedInnerIntegral
  dsimp only
  rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro v _
  unfold primeOrderedBuchstabWeight
  ring

theorem fourthRowTripleNoGate_integrable (eleven : Bool) {φ : ℝ} (hφ : 2 ≤ φ) :
    (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ u ∈ Icc (100 / 291 : ℝ) (2 / 5),
      IntervalIntegrable (fun v => buchstab ((φ - t - u - v) / u) / (t * u ^ 2 * v))
        volume u (2 / 5)) ∧
    (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2),
      IntervalIntegrable (fun u => ∫ v in u..(2 / 5),
        buchstab ((φ - t - u - v) / u) / (t * u ^ 2 * v))
        volume (100 / 291) (2 / 5)) ∧
    IntervalIntegrable (fun t => ∫ u in (100 / 291 : ℝ)..(2 / 5),
      ∫ v in u..(2 / 5), buchstab ((φ - t - u - v) / u) / (t * u ^ 2 * v))
        volume (fourthRowTripleNoGateLower eleven) (fourthRowTripleNoGateUpper eleven) := by
  have hP : 0 ≤ 1000 * φ + 200 := by linarith
  have hw := primeOrdered_buchstab_weight hφ (le_refl φ)
  have hi := primeOrdered_inner_regular hw (by norm_num) hP
    (by norm_num : (2 / 5 : ℝ) ∈ Icc (1 / 10) (1 / 2))
  have hm := fourthRowTripleNoGate_middle_regular hw (by norm_num) hP
  have heq (t u : ℝ) :
      (∫ v in u..(2 / 5), buchstab ((φ - t - u - v) / u) / (t * u ^ 2 * v)) =
        primeOrderedInnerIntegral (2 / 5) (primeOrderedBuchstabWeight φ) t u / u / t := by
    unfold primeOrderedInnerIntegral primeOrderedBuchstabWeight
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div]
    congr 1
    funext v
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro t ht u hu
    have hu' : u ∈ Icc (1 / 10 : ℝ) (1 / 2) := by
      constructor <;> linarith [hu.1, hu.2]
    have hh := (primeOrdered_integrable
      (primeOrdered_continuous_of_lipschitz (hw.third t ht u hu')) hu'
      (by norm_num : (2 / 5 : ℝ) ∈ Icc (1 / 10) (1 / 2))).div_const u
    have hh' := hh.div_const t
    convert hh' using 1
    funext v
    unfold primeOrderedBuchstabWeight
    ring
  · intro t ht
    simp_rw [heq]
    exact (primeOrdered_integrable
      (primeOrdered_continuous_of_lipschitz (hi.2.2 t ht))
      (by norm_num) (by norm_num)).div_const t
  · have he := fourthRowTripleNoGate_endpoints eleven
    simp_rw [heq, intervalIntegral.integral_div]
    exact primeOrdered_integrable (primeOrdered_continuous_of_lipschitz hm.2)
      ⟨he.1, he.2.1.trans he.2.2⟩ ⟨he.1.trans he.2.1, he.2.2⟩

theorem fourthRowTripleNoGate_integral_bounds (eleven : Bool) {φ : ℝ} (hφ : 2 ≤ φ) :
    0 ≤ fourthRowTripleNoGateIntegral eleven φ ∧
      fourthRowTripleNoGateIntegral eleven φ ≤ 640 := by
  have he := fourthRowTripleNoGate_endpoints eleven
  constructor
  · unfold fourthRowTripleNoGateIntegral
    apply intervalIntegral.integral_nonneg he.2.1
    intro t ht
    apply intervalIntegral.integral_nonneg (by norm_num : (100 / 291 : ℝ) ≤ 2 / 5)
    intro u hu
    apply intervalIntegral.integral_nonneg hu.2
    intro v hv
    exact (omega3XIntegralKernel_bounds hφ
      ⟨he.1.trans ht.1, ht.2.trans he.2.2⟩
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
      ⟨by linarith [hu.1, hv.1], by linarith [hv.2]⟩).1
  · rw [fourthRowTripleNoGate_integral_eq]
    have hm := fourthRowTripleNoGate_middle_regular
      (primeOrdered_buchstab_weight hφ (le_refl φ)) (by norm_num)
      (by linarith : 0 ≤ 1000 * φ + 200)
    have hh := primeOrdered_integral_norm_le_four
      ⟨he.1, he.2.1.trans he.2.2⟩ ⟨he.1.trans he.2.1, he.2.2⟩
      (by norm_num : (0 : ℝ) ≤ 16 * 10) hm.1
    norm_num only [show (4 * (16 * 10) : ℝ) = 640 by norm_num] at hh
    exact (le_abs_self _).trans hh

theorem fourthRowTripleNoGate_image_nonempty (eleven : Bool) :
    (fourthRowTripleNoGateIntegral eleven '' Ici 2).Nonempty :=
  ⟨_, mem_image_of_mem _ (show (2 : ℝ) ∈ Ici 2 by simp)⟩

theorem fourthRowTripleNoGate_image_bounded (eleven : Bool) :
    BddAbove (fourthRowTripleNoGateIntegral eleven '' Ici 2) := by
  refine ⟨640, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  exact (fourthRowTripleNoGate_integral_bounds eleven hφ).2

theorem fourthRowTripleNoGate_le_envelope (eleven : Bool) {φ : ℝ} (hφ : 2 ≤ φ) :
    fourthRowTripleNoGateIntegral eleven φ ≤ fourthRowTripleNoGateEnvelope eleven :=
  le_csSup (fourthRowTripleNoGate_image_bounded eleven) (mem_image_of_mem _ hφ)

theorem fourthRowTripleNoGate_envelope_bounds (eleven : Bool) :
    0 ≤ fourthRowTripleNoGateEnvelope eleven ∧ fourthRowTripleNoGateEnvelope eleven ≤ 640 := by
  refine ⟨((fourthRowTripleNoGate_integral_bounds eleven (le_refl 2)).1).trans
    (fourthRowTripleNoGate_le_envelope eleven (le_refl 2)), ?_⟩
  apply csSup_le (fourthRowTripleNoGate_image_nonempty eleven)
  rintro _ ⟨φ, hφ, rfl⟩
  exact (fourthRowTripleNoGate_integral_bounds eleven hφ).2

end Wu2008DoubleSieve
