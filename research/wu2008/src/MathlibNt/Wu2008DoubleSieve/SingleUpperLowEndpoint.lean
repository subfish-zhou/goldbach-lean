import MathlibNt.Wu2008DoubleSieve.SingleUpperLowQuadrature

namespace Wu2008DoubleSieve.SingleUpperLowEndpoint
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open SingleUpperCounts SingleUpperSplice SingleUpperLowPacking
open SingleUpperQuadrature SingleUpperPrimePayment SingleUpperLowQuadrature
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The density has genuine interval integrability throughout the enlarged slab. -/
theorem density_integrable {δ a b : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100)
    (ha : 1/15 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/3) :
    IntervalIntegrable (fun t => weight δ t/t) volume a b := by
  obtain ⟨M,K,_hM,_hK,hreg⟩ := weight_regular
  have hc := (hreg δ hδ hδhi).1.div continuousOn_id
    (fun t ht => ne_of_gt (show 0 < t by linarith [ht.1]))
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact hc.mono (fun t ht => ⟨ha.trans ht.1,ht.2.trans hb⟩)

/-- The original classical low integral is nonnegative, without a count hypothesis. -/
theorem low_integral_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100) :
    0 ≤ ∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), weight δ t/t := by
  have hab : truncatedSixthLowerAlpha ≤ (1/2-δ)/2 := by
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  apply intervalIntegral.integral_nonneg hab
  intro t ht
  have ht' : t ∈ Icc (1/15 : ℝ) (1/3) := by
    constructor
    · exact (by norm_num [truncatedSixthLowerAlpha] : (1/15 : ℝ) ≤ truncatedSixthLowerAlpha).trans ht.1
    · linarith [ht.2]
  exact div_nonneg (weight_nonneg hδ hδhi ht') (by linarith [ht'.1])

/-- The short lower overhang costs at most 15 M h, in the original N coordinate. -/
theorem overhang_upper : ∃ M : ℝ, 0 < M ∧
    ∀ δ a h : ℝ, 0 ≤ δ → δ ≤ 1/100 → 1/15 ≤ a →
      a ≤ truncatedSixthLowerAlpha → truncatedSixthLowerAlpha-a ≤ h →
    (∫ t in a..((1/2-δ)/2), weight δ t/t) ≤
      (∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), weight δ t/t) + 15*M*h := by
  obtain ⟨M,K,hM,_hK,hreg⟩ := weight_regular
  refine ⟨M,hM,?_⟩
  intro δ a h hδ hδhi ha haα hgap
  have hα : (1/15 : ℝ) ≤ truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have hαb : truncatedSixthLowerAlpha ≤ (1/2-δ)/2 := by
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hb : (1/2-δ)/2 ≤ 1/3 := by linarith
  have hαhi : truncatedSixthLowerAlpha ≤ (1/3 : ℝ) := by norm_num [truncatedSixthLowerAlpha]
  have hi1 := density_integrable hδ hδhi ha haα hαhi
  have hi2 := density_integrable hδ hδhi hα hαb hb
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hbound : |∫ t in a..truncatedSixthLowerAlpha, weight δ t/t| ≤
      15*M*(truncatedSixthLowerAlpha-a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := truncatedSixthLowerAlpha) (C := 15*M)
      (f := fun t => weight δ t/t) (fun t ht => by
        rw [uIoc_of_le haα] at ht
        have ht' : t ∈ Icc (1/15 : ℝ) (1/3) := ⟨ha.trans ht.1.le,ht.2.trans hαhi⟩
        have ht0 : 0 < t := by linarith [ht'.1]
        rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
        apply (div_le_iff₀ ht0).mpr
        have hmt := mul_le_mul_of_nonneg_left ht'.1 (show 0 ≤ 15*M by positivity)
        have hwt := (hreg δ hδ hδhi).2.1 t ht'
        nlinarith)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr haα)] using hh
  have hh := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 15*M by positivity)
  linarith [le_abs_self (∫ t in a..truncatedSixthLowerAlpha, weight δ t/t)]

/-- One scalar is chosen before all arithmetic thresholds. -/
theorem scalar_budget (I B ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ 4*(1+t)^2*(I+B*t) ≤ 4*I+ε := by
  have hc : ContinuousAt (fun t : ℝ => 4*(1+t)^2*(I+B*t)) 0 := by fun_prop
  obtain ⟨u,hu,hbound⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨u/2,by positivity,?_⟩
  have hh := hbound (x := u/2) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hu)]
    linarith)
  simp only [add_zero, mul_zero, one_pow, mul_one, Real.dist_eq] at hh
  linarith [(abs_lt.mp hh).2]

/-- The actual complete low count is bounded by the original classical integral.
Delta is chosen only after N; all errors and all cutoffs were fixed earlier. -/
theorem lowCount_classical_upper {δ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ r : ℝ,
      lowCount N δ r ≤
        (4*(∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), weight δ t/t)+ε) *
          truncatedSixthMassScale N := by
  obtain ⟨L,hL,hPrime⟩ := packing_prime_upper
  obtain ⟨M,hM,hOver⟩ := overhang_upper
  let I := ∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), weight δ t/t
  let B := 15*M+1+50*(L/truncatedSixthLowerAlpha+1)
  have hα : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hI : 0 ≤ I := low_integral_nonneg hδ.le hδhi
  obtain ⟨t,ht,hbudget⟩ := scalar_budget I B ε hε
  obtain ⟨TL,hTL4,hLow⟩ := low_packing_upper hδ hδhi ht
  obtain ⟨TP,_hTP4,hP⟩ := hPrime t ht
  obtain ⟨TQ,_hTQ4,hQ⟩ := weighted_prime_quadrature ht
  have hgap : 0 < truncatedSixthLowerAlpha-(1/15 : ℝ) := by norm_num [truncatedSixthLowerAlpha]
  obtain ⟨TH,_hTH4,hH⟩ := mesh_small (lt_min ht hgap)
  obtain ⟨TI,_hTI4,hLi⟩ := trueLi_upper ht
  refine ⟨max TL (max TP (max TQ (max TH TI))),hTL4.trans (le_max_left _ _),?_⟩
  intro N hN he r
  have hNL : TL ≤ N := (le_max_left _ _).trans hN
  have htail : max TP (max TQ (max TH TI)) ≤ N := (le_max_right _ _).trans hN
  have hNP : TP ≤ N := (le_max_left _ _).trans htail
  have htail' : max TQ (max TH TI) ≤ N := (le_max_right _ _).trans htail
  have hNQ : TQ ≤ N := (le_max_left _ _).trans htail'
  have htail'' : max TH TI ≤ N := (le_max_right _ _).trans htail'
  have hNH : TH ≤ N := (le_max_left _ _).trans htail''
  have hNI : TI ≤ N := (le_max_right _ _).trans htail''
  have hN4 := hTL4.trans hNL
  have hN2 : 2 ≤ N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN2
  have hlog := log_pos hNr
  let Δ := 1+log (N : ℝ)^(-4 : ℝ)
  have hpΔ : 0 < log (N : ℝ)^(-4 : ℝ) := rpow_pos_of_pos hlog _
  have hΔ : 1 < Δ := by dsimp [Δ]; linarith
  have hΔlo : 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ := le_rfl
  have hΔhi : Δ < 1+2*log (N : ℝ)^(-4 : ℝ) := by dsimp [Δ]; linarith
  have hmesh := hH N hNH Δ hΔlo hΔhi
  have hmesh_t : gamma5GainStep N Δ ≤ t := hmesh.trans (min_le_left _ _)
  have hmesh_gap : gamma5GainStep N Δ ≤ truncatedSixthLowerAlpha-1/15 :=
    hmesh.trans (min_le_right _ _)
  have hstart := packing_start_bounds hN2 hδhi hΔ
  have ha : 1/15 ≤ packingStart N δ Δ := by linarith [hstart.1]
  have hαb : truncatedSixthLowerAlpha ≤ (1/2-δ)/2 := by
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hab : packingStart N δ Δ ≤ (1/2-δ)/2 := hstart.2.le.trans hαb
  have hb : (1/2-δ)/2 ≤ 1/3 := by linarith
  have hpack := hP N hNP δ t Δ (packingStart N δ Δ) (packingSize N δ Δ)
    hδ.le hδhi ht.le hΔ ha (by rw [packing_endpoint]; exact hb)
  rw [packing_endpoint] at hpack
  have hquad := hQ N hNQ δ (packingStart N δ Δ) ((1/2-δ)/2)
    hδ.le hδhi ha hab hb
  have hover := hOver δ (packingStart N δ Δ) (gamma5GainStep N Δ)
    hδ.le hδhi ha hstart.2.le (by linarith [hstart.1])
  have hbracket : (∑ p ∈ primesIcc ((N : ℝ)^packingStart N δ Δ) ((N : ℝ)^((1/2-δ)/2)),
      weight δ (log p/log N)/(p : ℝ)) +
      50*(L*gamma5GainStep N Δ/truncatedSixthLowerAlpha+t) ≤ I+B*t := by
    have hfirst : (∑ p ∈ primesIcc ((N : ℝ)^packingStart N δ Δ) ((N : ℝ)^((1/2-δ)/2)),
        weight δ (log p/log N)/(p : ℝ)) ≤ I+15*M*gamma5GainStep N Δ+t := by
      dsimp [I]
      linarith [(abs_lt.mp hquad).2]
    have hpayM := mul_le_mul_of_nonneg_left hmesh_t (show 0 ≤ 15*M by positivity)
    have hpayL := mul_le_mul_of_nonneg_left hmesh_t (div_nonneg hL.le hα.le)
    have heq : I+B*t = I+15*M*t+t+50*(L*t/truncatedSixthLowerAlpha+t) := by
      dsimp [B]
      ring
    rw [heq]
    simp only [div_mul_eq_mul_div] at hpayL
    linarith only [hfirst,hpayM,hpayL]
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast hN2)
  have hnorm0 : 0 ≤ 4*logarithmicIntegral N*wuSingularSeries N/log N := by positivity
  have hscale : 0 ≤ truncatedSixthMassScale N := by
    unfold truncatedSixthMassScale
    positivity
  have hnorm : 4*logarithmicIntegral N*wuSingularSeries N/log N ≤
      4*(1+t)*truncatedSixthMassScale N := by
    calc
      _ = logarithmicIntegral N*(4*wuSingularSeries N/log N) := by ring
      _ ≤ ((1+t)*(N : ℝ)/log N)*(4*wuSingularSeries N/log N) :=
        mul_le_mul_of_nonneg_right (hLi N hNI) (by positivity)
      _ = _ := by unfold truncatedSixthMassScale; ring
  have hpositive : 0 ≤ I+B*t := add_nonneg hI (mul_nonneg hB ht.le)
  calc
    lowCount N δ r ≤ packingMass N δ t Δ (packingStart N δ Δ) (packingSize N δ Δ) :=
      hLow N hNL he Δ hΔlo hΔhi r
    _ ≤ (4*logarithmicIntegral N*wuSingularSeries N/log N)*(1+t)*
        ((∑ p ∈ primesIcc ((N : ℝ)^packingStart N δ Δ) ((N : ℝ)^((1/2-δ)/2)),
          weight δ (log p/log N)/(p : ℝ)) +
          50*(L*gamma5GainStep N Δ/truncatedSixthLowerAlpha+t)) := hpack
    _ ≤ (4*logarithmicIntegral N*wuSingularSeries N/log N)*(1+t)*(I+B*t) :=
      mul_le_mul_of_nonneg_left hbracket (mul_nonneg hnorm0 (by positivity))
    _ ≤ (4*(1+t)*truncatedSixthMassScale N)*(1+t)*(I+B*t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm (by positivity)) hpositive
    _ = (4*(1+t)^2*(I+B*t))*truncatedSixthMassScale N := by ring
    _ ≤ (4*I+ε)*truncatedSixthMassScale N := mul_le_mul_of_nonneg_right hbudget hscale

end Wu2008DoubleSieve.SingleUpperLowEndpoint
