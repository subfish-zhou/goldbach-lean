import Wu18938Campaign.M1.Confirmed.OmegaBuchstab
import Wu18938Campaign.M1.Confirmed.OmegaSwitching
import Wu18938Campaign.M1.Confirmed.PayloadNormalization
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalGamma9IntegralUpper

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Omega

open Wu2008DoubleSieve Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem buchstab_ordered {m i N d : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    (∑ p ∈ omega3XPrimes N δ s t d,
      let x := omega3XScale N d p.1 p.2.1 p.2.2
      x * buchstab (log x / log p.2.1) / log p.2.1) ≤
      (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
        primeOrderedTripleSum ((N : ℝ) ^ (1 / 2 - δ) / d) (1 / t) (1 / s)
          (primeOrderedBuchstabWeight (omega3XPhi N d δ)) := by
  let R := (N : ℝ) ^ (1 / 2 - δ) / d
  have hR := (hb.support_geometry hN hη hδ hd).2.2.1
  have hd0 := hb.support_pos hd
  have hg := roughBox_log_geometry hb hN hη hδ hd
  have hφ : 2 ≤ omega3XPhi N d δ := by linarith [hg.2.2.1]
  have hA : 1 / 10 ≤ 1 / t := one_div_le_one_div_of_le (by linarith) ht
  have hB : 1 / s ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hs
  let f := fun p1 p2 p3 : ℕ =>
    (N : ℝ) / ((d : ℝ) * log R) *
      (primeOrderedBuchstabWeight (omega3XPhi N d δ)
        (log p1 / log R) (log p2 / log R) (log p3 / log R) / ((p1 : ℝ) * p2 * p3))
  have hf : ∀ p1 ∈ primesIcc (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      ∀ p2 ∈ primesIoc (p1 : ℝ) (wuLocalCutoff N δ d s),
      ∀ p3 ∈ primesIoc (p2 : ℝ) (wuLocalCutoff N δ d s), 0 ≤ f p1 p2 p3 := by
    intro p1 hp1 p2 hp2 p3 hp3
    have hR0 : 0 ≤ R := by linarith
    have h1 := (mem_primesIcc (rpow_nonneg hR0 (1 / s))).mp hp1
    have h2 := (mem_primesIoc (rpow_nonneg hR0 (1 / s))).mp hp2
    have h3 := (mem_primesIoc (rpow_nonneg hR0 (1 / s))).mp hp3
    have hm1 := omega3XPrime_coordinate_mem hR hp1
    have hm2 := omega3XPrime_coordinate_mem hR ((mem_primesIcc
      (rpow_nonneg hR0 (1 / s))).mpr ⟨h2.1,h1.2.1.trans h2.2.1.le,h2.2.2⟩)
    have hm3 := omega3XPrime_coordinate_mem hR ((mem_primesIcc
      (rpow_nonneg hR0 (1 / s))).mpr
        ⟨h3.1,(h1.2.1.trans h2.2.1.le).trans h3.2.1.le,h3.2.2⟩)
    have hw := buchstab_pos (omega3X_argument_bounds hφ
      ⟨hA.trans hm1.1,hm1.2.trans hB⟩ ⟨hA.trans hm2.1,hm2.2.trans hB⟩
      ⟨hA.trans hm3.1,hm3.2.trans hB⟩).2.2
    have hlR := log_pos hR
    have hl2 : 0 < log (p2 : ℝ) := log_pos (by exact_mod_cast h2.1.one_lt)
    dsimp [f,primeOrderedBuchstabWeight]
    positivity
  calc
    _ = ∑ p ∈ omega3XPrimes N δ s t d, f p.1 p.2.1 p.2.2 := by
      apply sum_congr rfl
      intro p hp
      have h := mem_omega3XPrimes.mp hp
      exact omega3XPrime_buchstab_term_eq (by omega) hd0
        (mem_primeWindow.mp h.2.1).1 (mem_primeWindow.mp h.1).1 h.2.2.2.1 hR
    _ ≤ _ := (omega3XPrime_sum_le_nested f hf).trans_eq (by
      simp only [primeOrderedTripleSum,mul_sum,f,wuLocalCutoff,R])

theorem ordered_uniform (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      |primeOrderedTripleSum ((N : ℝ) ^ (1 / 2 - δ) / d) (1 / t) (1 / s)
          (primeOrderedBuchstabWeight (omega3XPhi N d δ)) -
        omega3XIntegral s t (omega3XPhi N d δ)| < ε := by
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp
    (primeOrdered_buchstab_uniform (max 2 (1 / η)) ε (le_max_left _ _) he)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop R0))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN i Δ V hb d hd s t hs hst ht
  have hg := roughBox_log_geometry hb (by omega) hη hδ hd
  exact hR0 _ ((hT N (by omega)).trans (hb.remaining d hd)) _ _ _
    (by linarith [hg.2.2.1]) (hg.2.2.2.trans (le_max_right _ _))
    (one_div_le_one_div_of_le (by linarith) ht)
    (one_div_le_one_div_of_le (by linarith) hst)
    (one_div_le_one_div_of_le (by norm_num) hs)

theorem integral_mass_eq (N : ℕ) (δ Δ s t : ℝ) {i : ℕ} (V : Fin i → ℝ) :
    omega3XIntegralMain N δ s t (convolutionWuWindows N Δ V) =
      HighSourcePayload.mass N δ Δ V (fun d => omega3XIntegral s t (omega3XPhi N d δ)) := by
  unfold omega3XIntegralMain HighSourcePayload.mass
  rw [mul_sum]
  exact sum_congr rfl (fun _ _ => by ring)

theorem buchstab_integral (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      omega3XBuchstabMain N δ s t (convolutionWuWindows N Δ V) ≤
        omega3XIntegralMain N δ s t (convolutionWuWindows N Δ V) +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := ordered_uniform m hη hδ (mul_pos he hη)
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have hf : omega3XBuchstabMain N δ s t (convolutionWuWindows N Δ V) ≤
      HighSourcePayload.mass N δ Δ V (fun d =>
        primeOrderedTripleSum ((N : ℝ) ^ (1 / 2 - δ) / d) (1 / t) (1 / s)
          (primeOrderedBuchstabWeight (omega3XPhi N d δ))) := by
    unfold omega3XBuchstabMain HighSourcePayload.mass
    apply sum_le_sum
    intro d hd
    have hh := mul_le_mul_of_nonneg_left (buchstab_ordered hb (by omega) hη hδ hd hs hst ht)
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
    convert hh using 1
    ring
  have herr := (abs_le.mp (roughBox_payload_error hb (by omega) hη hδ he.le
    (fun d => primeOrderedTripleSum ((N : ℝ) ^ (1 / 2 - δ) / d) (1 / t) (1 / s)
      (primeOrderedBuchstabWeight (omega3XPhi N d δ)))
    (fun d => omega3XIntegral s t (omega3XPhi N d δ))
    (fun d hd => (hT N hN i Δ V hb d hd s t hs hst ht).le))).2
  rw [← integral_mass_eq] at herr
  linarith only [hf,herr]

theorem X_integral (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      omega3SieveX N δ s t (convolutionWuWindows N Δ V) ≤
        omega3XIntegralMain N δ s t (convolutionWuWindows N Δ V) +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := X_buchstab m hη hδ (half_pos he)
  obtain ⟨T1,_,h1⟩ := buchstab_integral m hη hδ (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have hX := h0 N (by omega) i Δ V hb s t hs hst ht
  have hI := h1 N (by omega) i Δ V hb s t hs hst ht
  linarith only [hX,hI]

theorem integral_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      wuOmega3Sum N δ s t (convolutionWuWindows N Δ V) ≤
        omega3XIntegralMain N δ s t (convolutionWuWindows N Δ V) *
          (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
            wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let A := (1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))
  have hA : 0 < A := mul_pos (mul_pos (by linarith) (by positivity))
    (div_pos (by norm_num) (by linarith))
  have he3 : 0 < ε / 3 := by positivity
  obtain ⟨T0,hT04,h0⟩ := source_switching m hη hδ he3
  obtain ⟨T1,_,h1⟩ := switched_density m hη hδ hδhi hρ he3
  obtain ⟨T2,_,h2⟩ := X_integral m hη hδ (show 0 < (2 * ε / 3) / A by positivity)
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht
  have hC : 0 ≤ wuSingularSeries N / log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hf := h0 N (by omega) heven i Δ V hb s t hs hst ht
  have hd := h1 N (by omega) heven i Δ V hb s t hs hst ht
  have hr := h2 N (by omega) i Δ V hb s t hs hst ht
  have ht' := mul_le_mul_of_nonneg_left (roughBox_reciprocal_theta hb (by omega) hη hδ)
    (show 0 ≤ 2 * ε / 3 by positivity)
  have hh := mul_le_mul_of_nonneg_right hr (mul_nonneg hA.le hC)
  simp only [add_mul] at hh
  have hcancel : (((2 * ε / 3) / A) * ((N : ℝ) / log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) * (A * (wuSingularSeries N / log N)) =
      (2 * ε / 3) * (wuSingularSeries N / log N * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) := by field_simp
  rw [hcancel] at hh
  rw [mul_div_assoc] at hd ⊢
  linarith only [hf,hd,hh,ht']

theorem source_theta (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      wuOmega3Sum N δ s t (convolutionWuWindows N Δ V) ≤
        (2 / (1 - 2 * δ)) *
          HighSourcePayload.theta N δ Δ V (fun d => omega3XIntegral s t (omega3XPhi N d δ)) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨ρ,hr,T0,hT04,h0⟩ := roughBox_payload_density_slack m hη hδ hδhi
    (by norm_num : (0 : ℝ) ≤ 10000) (half_pos he)
  obtain ⟨T1,_,h1⟩ := integral_density m hη hδ hδhi hr (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht
  have hd := h1 N (by omega) heven i Δ V hb s t hs hst ht
  have hpay := h0 N (by omega) i Δ V hb
    (fun d => omega3XIntegral s t (omega3XPhi N d δ)) (by
      intro d hd
      have hg := roughBox_log_geometry hb (by omega) hη hδ hd
      have hphi : 2 ≤ omega3XPhi N d δ := by linarith [hg.2.2.1]
      exact ⟨omega3XIntegral_nonneg hs hst ht hphi,
        (omega3XIntegral_le_envelope hs hst ht hphi).trans
          (omega3XIntegralEnvelope_uniform_cap hs hst ht).2⟩)
  rw [← integral_mass_eq] at hpay
  rw [mul_div_assoc] at hd
  nlinarith only [hd,hpay]

end Wu18938Campaign.M1.Confirmed.Omega
