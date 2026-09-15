import MathlibNt.Wu2008DoubleSieve.HighSixPrimePayment

namespace Wu2008DoubleSieve.HighSix
open Finset Real Filter Set
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def clippedLog (η u : ℝ) : ℝ := log (max 2 u-1)-4*η
noncomputable def kernelMass : ℝ := ∫ u in (1-1/s)..(1-1/S), 1/(u*(1-u))
noncomputable def thetaAtom (N : ℕ) (δ : ℝ) (p : ℕ) : ℝ :=
  4*logarithmicIntegral N*wuSingularSeries (p*N)/((Nat.totient p : ℝ)*log (R N δ p))

theorem clippedLog_monotone (η : ℝ) : Monotone (clippedLog η) := by
  intro x y hxy
  apply sub_le_sub_right
  apply log_le_log (by have := le_max_left (2 : ℝ) x; linarith)
  exact sub_le_sub_right (max_le_max_left 2 hxy) 1

theorem clippedLog_bound {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    {u : ℝ} (hu : u ∈ Icc (1 : ℝ) 10) : |clippedLog η u| ≤ 14 := by
  have hm : 1 ≤ max 2 u-1 := by have := le_max_left (2 : ℝ) u; linarith
  have hM : max 2 u ≤ 10 := max_le (by norm_num) hu.2
  have hl0 := log_nonneg hm
  have hl1 := log_le_sub_one_of_pos (by linarith : 0 < max 2 u-1)
  unfold clippedLog
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem integral_domain {u : ℝ} (hu : u ∈ uIcc (1-1/s) (1-1/S)) :
    0 < u ∧ u < 1 ∧ 2 ≤ S*u := by
  have hab : 1-1/s ≤ 1-1/S := by norm_num [s,S]
  rw [uIcc_of_le hab] at hu
  have hmul := mul_le_mul_of_nonneg_left hu.1 (show 0 ≤ S by norm_num [S])
  norm_num [s,S] at hu hmul ⊢
  exact ⟨by linarith [hu.1], by linarith [hu.2], by linarith⟩

theorem kernel_integrable : IntervalIntegrable (fun u : ℝ => 1/(u*(1-u)))
    MeasureTheory.volume (1-1/s) (1-1/S) := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
  intro u hu
  exact mul_ne_zero (integral_domain hu).1.ne' (by change 1-u ≠ 0; linarith [(integral_domain hu).2.1])

theorem log_kernel_integrable : IntervalIntegrable (fun u : ℝ => log (S*u-1)/(u*(1-u)))
    MeasureTheory.volume (1-1/s) (1-1/S) := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · exact (continuousOn_const.mul continuousOn_id).sub continuousOn_const
    · intro u hu; linarith [(integral_domain hu).2.2]
  · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  · intro u hu
    exact mul_ne_zero (integral_domain hu).1.ne' (by change 1-u ≠ 0; linarith [(integral_domain hu).2.1])

/-- The signed normalization fee is integrated exactly, not multiplied by
an incorrectly oriented reciprocal lower bound. -/
theorem signed_integral (η : ℝ) :
    (∫ u in (1-1/s)..(1-1/S), clippedLog η (S*u)/(u*(1-u))) = J-4*η*kernelMass := by
  have he : (∫ u in (1-1/s)..(1-1/S), clippedLog η (S*u)/(u*(1-u))) =
      ∫ u in (1-1/s)..(1-1/S), log (S*u-1)/(u*(1-u))-4*η*(1/(u*(1-u))) := by
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [clippedLog, max_eq_right (integral_domain hu).2.2]
    ring
  rw [he, intervalIntegral.integral_sub log_kernel_integrable (kernel_integrable.const_mul _),
    intervalIntegral.integral_const_mul]
  rfl

theorem thetaAtom_nonneg {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N) : 0 ≤ thetaAtom N δ p := by
  have hli : 0 ≤ logarithmicIntegral N := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0
    (by norm_num) (by exact_mod_cast hN)
  have hC := wuSingularSeries_pos (p*N)
    (Nat.mul_pos (mem_primeWindow.mp hp).1.pos (by omega))
  have hl := log_pos (ratio_bounds hN hδ hδhi hp).1
  unfold thetaAtom
  positivity

theorem B6_sum (N : ℕ) (δ : ℝ) : B6 N δ = ∑ p ∈ P N, thetaAtom N δ p := by
  unfold B6 boxTheta thetaAtom R
  rw [mul_sum]
  simpa only [mul_div_assoc, boxConvolutionSupport, mul_left_comm] using
    SingleUpperCounts.single_weighted_sum (P N)
      (fun p => 4*logarithmicIntegral N*wuSingularSeries (p*N)/
        ((Nat.totient p : ℝ)*log ((N : ℝ)^(1/2-δ)/(p : ℝ))))

theorem argument_coordinate {N p q : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N) (hq : q.Prime) :
    argument N δ p q = S*(1-log q/log (R N δ p)) := by
  have hr := ratio_bounds hN hδ hδhi hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hl := (log_pos hr.1).ne'
  have hs : S ≠ 0 := by norm_num [S]
  have hlev : pairLevel N δ p q = R N δ p / q := by
    unfold pairLevel R; rw [Nat.cast_mul, div_div]
  unfold argument
  change log (pairLevel N δ p q)/log ((R N δ p)^(1/S)) = _
  rw [hlev, log_div (by linarith [hr.1] : R N δ p ≠ 0) hq0.ne',
    log_rpow (by linarith [hr.1] : 0 < R N δ p)]
  field_simp

theorem normalized_atom {N p q : ℕ} {δ η : ℝ} (hN : 2 ≤ N)
    (he : Even N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N)
    (hq : q ∈ primeWindow N (z N δ p) (w N δ p)) :
    (logarithmicIntegral N/(Nat.totient (p*q) : ℝ))*
      ((log (argument N δ p q-1)-4*η)*
        (4*wuSingularSeries ((p*q)*N)/log (pairLevel N δ p q))) =
    thetaAtom N δ p *
      (clippedLog η (S*(1-log q/log (R N δ p)))/
        (((q : ℝ)-2)*(1-log q/log (R N δ p)))) := by
  have harg := argument_bounds hN hδ hδhi hp hq
  have hc := argument_coordinate hN hδ hδhi hp (mem_primeWindow.mp hq).1
  have hlev : pairLevel N δ p q = R N δ p / q := by
    unfold pairLevel R; rw [Nat.cast_mul, div_div]
  have hl := reboxing_log_denominator (ratio_bounds hN hδ hδhi hp).1
    (show (0 : ℝ) < q by exact_mod_cast (mem_primeWindow.mp hq).1.pos)
  rw [hlev, hl, hc]
  have heuler := pair_euler_split hN he hδ hδhi hp hq
  have hh : 2 ≤ S*(1-log q/log (R N δ p)) := hc ▸ harg.2.1
  simp only [clippedLog, max_eq_right hh, thetaAtom]
  calc
    _ = 4*logarithmicIntegral N*(wuSingularSeries ((p*q)*N)/(Nat.totient (p*q) : ℝ))*
        (log (S*(1-log q/log (R N δ p))-1)-4*η)/
          (log (R N δ p)*(1-log q/log (R N δ p))) := by ring
    _ = _ := by rw [heuler]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- Uniform relative payment on the actual prime-pair sum. Both the signed
fee and quadrature error retain the same full outer Theta mass. -/
theorem normalized_integral_relative {δ η ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (J-4*η*kernelMass-ε)*B6 N δ ≤ normalizedMain N δ η := by
  obtain ⟨T,hT4,hT⟩ := moving_prime_integral hδ hδhi (show (0 : ℝ) ≤ 14 by norm_num) hε
  refine ⟨T,hT4,?_⟩
  intro N hN he
  have hN2 : 2 ≤ N := by omega
  rw [B6_sum, mul_sum]
  apply sum_le_sum
  intro p hp
  have hi := hT N hN p hp (clippedLog η) ((clippedLog_monotone η).monotoneOn _)
    (fun u hu => clippedLog_bound hη hη1 hu)
  rw [signed_integral] at hi
  have hlo : J-4*η*kernelMass-ε ≤ ∑ q ∈ primeWindow N (z N δ p) (w N δ p),
      clippedLog η (S*(1-log q/log (R N δ p)))/
        (((q : ℝ)-2)*(1-log q/log (R N δ p))) := by linarith [(abs_le.mp hi).1]
  calc
    _ ≤ thetaAtom N δ p * (∑ q ∈ primeWindow N (z N δ p) (w N δ p),
      clippedLog η (S*(1-log q/log (R N δ p)))/
        (((q : ℝ)-2)*(1-log q/log (R N δ p)))) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlo (thetaAtom_nonneg hN2 hδ hδhi hp)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      exact (normalized_atom hN2 he hδ hδhi hp hq).symm

end Wu2008DoubleSieve.HighSix
