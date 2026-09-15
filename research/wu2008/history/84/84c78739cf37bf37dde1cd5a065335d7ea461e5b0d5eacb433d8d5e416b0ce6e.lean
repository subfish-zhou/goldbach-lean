import SrcSingleAnalyticOmegaLower

noncomputable section
namespace WuSource.SrcSingle.Analytic
open Wu2008DoubleSieve Real Finset Filter Set
open scoped Classical Topology BigOperators Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

def J (j : Fin 7) (a : ℝ) : ℝ :=
  ∫ u in (1 - 1 / a)..(1 - 1 / psiTop j), log (psiTop j * u - 1) / (u * (1 - u))
def kernelMass (j : Fin 7) (a : ℝ) : ℝ :=
  ∫ u in (1 - 1 / a)..(1 - 1 / psiTop j), 1 / (u * (1 - u))

theorem coordinate_bounds {j : Fin 7} {N p q : ℕ} {δ a : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) (ha : psiNode j ≤ a) (hq0 : (0 : ℝ) < q)
    (hql : wuLocalCutoff N δ p (psiTop j) ≤ (q : ℝ))
    (hqu : (q : ℝ) ≤ wuLocalCutoff N δ p a) :
    2 ≤ psiTop j * (1 - log q / log (psiRatio N δ p)) ∧
      psiTop j * (1 - log q / log (psiRatio N δ p)) ≤ 4 := by
  have hr := (seven_ratio_geometry j hN hd hh hp).1
  have hR0 := zero_lt_one.trans hr
  have hlR := log_pos hr
  have hS : 0 < psiTop j := by linarith [(seven_parameter_geometry j).2.2.1]
  have hz := (seven_cutoff_geometry j hN hd hh hp).1
  have hloglo := log_le_log (zero_lt_one.trans hz) hql
  have hloghi := log_le_log hq0 hqu
  change log ((psiRatio N δ p) ^ (1 / psiTop j)) ≤ _ at hloglo
  change _ ≤ log ((psiRatio N δ p) ^ (1 / a)) at hloghi
  rw [log_rpow hR0] at hloglo hloghi
  have hlo : 1 / psiTop j ≤ log q / log (psiRatio N δ p) := (le_div_iff₀ hlR).mpr hloglo
  have hhi : log q / log (psiRatio N δ p) ≤ 1 / a := (div_le_iff₀ hlR).mpr hloghi
  have hblo := mul_le_mul_of_nonneg_left hlo hS.le
  have hbhi := mul_le_mul_of_nonneg_left hhi hS.le
  rw [mul_one_div_cancel hS.ne'] at hblo
  rw [mul_one_div] at hbhi
  exact ⟨by nlinarith only [hbhi, (parameter_lower ha).2.2],
    by nlinarith only [hblo, (seven_parameter_geometry j).2.2.2.1]⟩

theorem pair_euler_split {j : Fin 7} {N p q : ℕ} {δ a : ℝ}
    (hN : 2 ≤ N) (he : Even N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) (ha : psiNode j ≤ a) (hb : a ≤ psiTop j)
    (hq : q ∈ innerPrimes j N δ a p) :
    wuSingularSeries ((p * q) * N) / (Nat.totient (p * q) : ℝ) =
      wuSingularSeries (p * N) / ((Nat.totient p : ℝ) * ((q : ℝ) - 2)) := by
  obtain ⟨hqp, hqN, _, _⟩ := mem_primeWindow.mp hq
  have hq2 : 2 < q := by
    have h2N : 2 ∣ N := even_iff_two_dvd.mp he
    have hqn : q ≠ 2 := by
      intro h; subst q
      exact (hqp.coprime_iff_not_dvd.mp hqN) h2N
    have := hqp.two_le
    omega
  have hqpnd : ¬q ∣ p := by
    intro hdvd
    rcases (Nat.dvd_prime (mem_primeWindow.mp hp).1).mp hdvd with h | h
    · exact hqp.ne_one h
    · exact (Nat.ne_of_lt (inner_lt_outer hN hd hh hp ha hb hq)) h
  rw [wu_inserted_arithmetic_weight (by omega) (mem_primeWindow.mp hp).1.pos hqp hq2 hqN,
    if_neg hqpnd]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem moving_prime_integral {δ B ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hB : 0 ≤ B) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (j : Fin 7) (a : ℝ), psiNode j ≤ a → a ≤ psiTop j → ∀ p ∈ psiPrimes j N,
      ∀ f : ℝ → ℝ, MonotoneOn f (Set.Icc 1 10) →
      (∀ u ∈ Set.Icc (1 : ℝ) 10, |f u| ≤ B) →
      |(∑ q ∈ innerPrimes j N δ a p,
        f (psiTop j * (1 - log q / log (psiRatio N δ p))) /
          (((q : ℝ) - 2) * (1 - log q / log (psiRatio N δ p)))) -
        ∫ u in (1 - 1 / a)..(1 - 1 / psiTop j), f (psiTop j * u) / (u * (1 - u))| ≤ ε := by
  obtain ⟨Q0, _, hprime⟩ := omega2_source_prime_integral_uniform hB (half_pos heps)
  obtain ⟨T1, hdelete⟩ := primeCoefficient_all_to_coprime_uniform
    (show (0 : ℝ) < 1 / 40 by norm_num) hB (half_pos heps)
  have hexp : 0 < (1 / 2 - δ - 1 / 3 : ℝ) := by linarith
  have hgrow : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 - δ - 1 / 3)) atTop atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp (hgrow.eventually (eventually_ge_atTop Q0))
  refine ⟨max 4 (max T1 T2), le_max_left _ _, fun N hN j a ha hb p hp f hf hfb => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hr := seven_ratio_geometry j hN2 hd hh hp
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hQ : Q0 ≤ psiRatio N δ p := by
    apply (hT2 N (by omega)).trans
    apply (rpow_le_rpow_of_exponent_le hNr _).trans hr.2.2
    unfold levelExponent
    linarith [(seven_parameter_geometry j).2.2.2.2.2.2.2.2.2.1]
  have hprime' := hprime (psiRatio N δ p) hQ f hf hfb a (psiTop j)
    (by linarith [(seven_parameter_geometry j).1]) hb
    (seven_parameter_geometry j).2.2.1 (seven_parameter_geometry j).2.2.2.1
  have hbound (q : ℕ)
      (hq : q ∈ primeWindow 1 (wuLocalCutoff N δ p (psiTop j)) (wuLocalCutoff N δ p a)) :
      |f (psiTop j * (1 - log q / log (psiRatio N δ p)))| ≤ B := by
    have hc := coordinate_bounds hN2 hd hh hp ha
      (by exact_mod_cast (mem_primeWindow.mp hq).1.pos)
      (mem_primeWindow.mp hq).2.2.1 (mem_primeWindow.mp hq).2.2.2.le
    exact hfb _ ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have hdelete' := hdelete N (by omega) (psiRatio N δ p)
    (wuLocalCutoff N δ p (psiTop j)) (wuLocalCutoff N δ p a)
    (fun q => f (psiTop j * (1 - log q / log (psiRatio N δ p)))) hr.1
    (cutoff_range hN2 hd hh hp (seven_parameter_geometry j).2.2.2.2.1 le_rfl).1
    (rpow_le_rpow_of_exponent_le hr.1.le
      ((div_le_iff₀ (parameter_lower ha).1).mpr (by linarith [(seven_parameter_geometry j).1])))
    hbound
  change |(∑ q ∈ primeWindow 1 (wuLocalCutoff N δ p (psiTop j)) (wuLocalCutoff N δ p a), _) - _| ≤ ε / 2
    at hprime'
  exact (abs_sub_le _ _ _).trans
    ((add_le_add ((abs_sub_comm _ _).trans_le hdelete') hprime').trans (by linarith))

theorem integral_domain {j : Fin 7} {a u : ℝ} (ha : psiNode j ≤ a) (hb : a ≤ psiTop j)
    (hu : u ∈ uIcc (1 - 1 / a) (1 - 1 / psiTop j)) :
    0 < u ∧ u < 1 ∧ 2 ≤ psiTop j * u := by
  have hapos := (parameter_lower ha).1
  have hSpos : 0 < psiTop j := by linarith [(seven_parameter_geometry j).2.2.1]
  have hab : 1 - 1 / a ≤ 1 - 1 / psiTop j :=
    sub_le_sub_left (one_div_le_one_div_of_le hapos hb) 1
  rw [uIcc_of_le hab] at hu
  have hai : 1 / a < 1 := (div_lt_iff₀ hapos).mpr (by linarith [(seven_parameter_geometry j).1])
  have hSi := one_div_pos.mpr hSpos
  have hmul := mul_le_mul_of_nonneg_left hu.1 hSpos.le
  have hp := (parameter_lower ha).2.2
  rw [mul_sub, mul_one, mul_one_div] at hmul
  exact ⟨by linarith [hu.1], by linarith [hu.2], by linarith⟩

theorem kernel_integrable {j : Fin 7} {a : ℝ} (ha : psiNode j ≤ a) (hb : a ≤ psiTop j) :
    IntervalIntegrable (fun u : ℝ => 1 / (u * (1 - u))) MeasureTheory.volume
      (1 - 1 / a) (1 - 1 / psiTop j) := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
  intro u hu
  exact mul_ne_zero (integral_domain ha hb hu).1.ne'
    (by change 1 - u ≠ 0; linarith [(integral_domain ha hb hu).2.1])

theorem log_kernel_integrable {j : Fin 7} {a : ℝ} (ha : psiNode j ≤ a) (hb : a ≤ psiTop j) :
    IntervalIntegrable (fun u : ℝ => log (psiTop j * u - 1) / (u * (1 - u)))
      MeasureTheory.volume (1 - 1 / a) (1 - 1 / psiTop j) := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · exact (continuousOn_const.mul continuousOn_id).sub continuousOn_const
    · intro u hu; linarith [(integral_domain ha hb hu).2.2]
  · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  · intro u hu
    exact mul_ne_zero (integral_domain ha hb hu).1.ne'
      (by change 1 - u ≠ 0; linarith [(integral_domain ha hb hu).2.1])

theorem signed_integral {j : Fin 7} {a : ℝ}
    (ha : psiNode j ≤ a) (hb : a ≤ psiTop j) (η : ℝ) :
    (∫ u in (1 - 1 / a)..(1 - 1 / psiTop j),
      HighSix.clippedLog η (psiTop j * u) / (u * (1 - u))) =
        J j a - 4 * η * kernelMass j a := by
  have he :
      (∫ u in (1 - 1 / a)..(1 - 1 / psiTop j), HighSix.clippedLog η (psiTop j * u) / (u * (1 - u))) =
      ∫ u in (1 - 1 / a)..(1 - 1 / psiTop j),
        log (psiTop j * u - 1) / (u * (1 - u)) - 4 * η * (1 / (u * (1 - u))) := by
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [HighSix.clippedLog, max_eq_right (integral_domain ha hb hu).2.2]
    ring
  rw [he, intervalIntegral.integral_sub (log_kernel_integrable ha hb)
    ((kernel_integrable ha hb).const_mul _), intervalIntegral.integral_const_mul]
  rfl

theorem argument_coordinate {j : Fin 7} {N p q : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hp : p ∈ psiPrimes j N) (hq : q.Prime) :
    argument j N δ p q = psiTop j * (1 - log q / log (psiRatio N δ p)) := by
  have hr := (seven_ratio_geometry j hN hd hh hp).1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hl := (log_pos hr).ne'
  have hS : psiTop j ≠ 0 := by linarith [(seven_parameter_geometry j).2.2.1]
  unfold argument
  change log (pairLevel N δ p q) / log ((psiRatio N δ p) ^ (1 / psiTop j)) = _
  rw [pair_level_eq, log_div (by linarith : psiRatio N δ p ≠ 0) hq0.ne',
    log_rpow (by linarith : 0 < psiRatio N δ p)]
  field_simp

theorem normalized_atom {j : Fin 7} {N p q : ℕ} {δ a η : ℝ}
    (hN : 2 ≤ N) (he : Even N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) (ha : psiNode j ≤ a) (hb : a ≤ psiTop j)
    (hq : q ∈ innerPrimes j N δ a p) :
    logarithmicIntegral N / (Nat.totient (p * q) : ℝ) *
      ((log (argument j N δ p q - 1) - 4 * η) *
        (4 * wuSingularSeries ((p * q) * N) / log (pairLevel N δ p q))) =
      atom N δ p * (HighSix.clippedLog η (psiTop j * (1 - log q / log (psiRatio N δ p))) /
        (((q : ℝ) - 2) * (1 - log q / log (psiRatio N δ p)))) := by
  have harg := argument_bounds hN hd hh hp ha hq
  have hc := argument_coordinate hN hd hh hp (mem_primeWindow.mp hq).1
  have hl := reboxing_log_denominator (seven_ratio_geometry j hN hd hh hp).1
    (show (0 : ℝ) < q by exact_mod_cast (mem_primeWindow.mp hq).1.pos)
  rw [pair_level_eq, hl, hc]
  have heuler := pair_euler_split hN he hd hh hp ha hb hq
  have hcoord : 2 ≤ psiTop j * (1 - log q / log (psiRatio N δ p)) := hc ▸ harg.2.1
  simp only [HighSix.clippedLog, max_eq_right hcoord, atom]
  calc
    _ = 4 * logarithmicIntegral N *
        (wuSingularSeries ((p * q) * N) / (Nat.totient (p * q) : ℝ)) *
        (log (psiTop j * (1 - log q / log (psiRatio N δ p)) - 1) - 4 * η) /
        (log (psiRatio N δ p) * (1 - log q / log (psiRatio N δ p))) := by ring
    _ = _ := by rw [heuler]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem normalized_integral_relative {δ η ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heta : 0 ≤ η) (heta1 : η ≤ 1) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ (j : Fin 7) (a : ℝ),
      psiNode j ≤ a → a ≤ psiTop j →
      (J j a - 4 * η * kernelMass j a - ε) * theta j N δ ≤ normalizedPair j N δ a η := by
  obtain ⟨T, hT4, hT⟩ := moving_prime_integral hd hh (show (0 : ℝ) ≤ 14 by norm_num) heps
  refine ⟨T, hT4, fun N hN he j a ha hb => ?_⟩
  have hN2 : 2 ≤ N := by omega
  rw [theta_sum, mul_sum]
  apply sum_le_sum
  intro p hp
  have hi := hT N hN j a ha hb p hp (HighSix.clippedLog η)
    ((HighSix.clippedLog_monotone η).monotoneOn _)
    (fun u hu => HighSix.clippedLog_bound heta heta1 hu)
  rw [signed_integral ha hb] at hi
  have hlo : J j a - 4 * η * kernelMass j a - ε ≤ ∑ q ∈ innerPrimes j N δ a p,
      HighSix.clippedLog η (psiTop j * (1 - log q / log (psiRatio N δ p))) /
        (((q : ℝ) - 2) * (1 - log q / log (psiRatio N δ p))) := by
    linarith [(abs_le.mp hi).1]
  calc
    _ ≤ atom N δ p * (∑ q ∈ innerPrimes j N δ a p,
        HighSix.clippedLog η (psiTop j * (1 - log q / log (psiRatio N δ p))) /
          (((q : ℝ) - 2) * (1 - log q / log (psiRatio N δ p)))) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlo (atom_nonneg hN2 hd hh hp)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      exact (normalized_atom hN2 he hd hh hp ha hb hq).symm

theorem omega2_integral_paid {j : Fin 7} {a δ ε : ℝ}
    (ha : psiNode j ≤ a) (hb : a ≤ psiTop j)
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      J j a * theta j N δ - ε * truncatedSixthMassScale N ≤
        wuOmega2Sum N δ a (psiTop j) (fun _ : Fin 1 => psiPrimes j N) := by
  let η := min 1 (ε / (8960 * (|kernelMass j a| + 1)))
  have heta : 0 < η := lt_min (by norm_num) (by positivity)
  have heta1 : η ≤ 1 := min_le_left _ _
  have hbudget : η * (8960 * (|kernelMass j a| + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hcost : 4 * η * |kernelMass j a| + ε / 2240 ≤ ε / 1120 := by
    have := heta.le
    nlinarith
  obtain ⟨T1, hT14, hT1⟩ := normalized_integral_relative hd hh heta.le heta1
    (show 0 < ε / 2240 by positivity)
  obtain ⟨T2, _, hT2⟩ := theta_total_mass hd hh
  obtain ⟨T3, _, hT3⟩ := omega2_normalized_paid hd hh heta heta1 (half_pos heps)
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), fun N hN he => ?_⟩
  have hi := hT1 N (by omega) he j a ha hb
  have hm := hT2 N (by omega) j
  have ho := hT3 N (by omega) he j a ha hb
  have hs := truncatedSixthClosure_scale_nonneg (hT14.trans (by omega : T1 ≤ N))
  have hfee : (4 * η * kernelMass j a + ε / 2240) * theta j N δ ≤
      (ε / 2) * truncatedSixthMassScale N := by
    calc
      _ ≤ (4 * η * |kernelMass j a| + ε / 2240) * theta j N δ := by
        apply mul_le_mul_of_nonneg_right _ hm.1
        have := mul_le_mul_of_nonneg_left (le_abs_self (kernelMass j a))
          (show 0 ≤ 4 * η by positivity)
        linarith
      _ ≤ (4 * η * |kernelMass j a| + ε / 2240) * (560 * truncatedSixthMassScale N) :=
        mul_le_mul_of_nonneg_left hm.2 (by positivity)
      _ ≤ (ε / 1120) * (560 * truncatedSixthMassScale N) :=
        mul_le_mul_of_nonneg_right hcost (by positivity)
      _ = _ := by ring
  nlinarith only [hi, ho, hfee]

#check @omega2_integral_paid
#print axioms omega2_integral_paid
end WuSource.SrcSingle.Analytic
