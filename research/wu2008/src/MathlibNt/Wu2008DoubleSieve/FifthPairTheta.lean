import MathlibNt.Wu2008DoubleSieve.FifthPairProducer
namespace Wu2008DoubleSieve
open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem fifthPair_cell_theta_lower {N : ℕ} {δ a b c d : ℝ}
    (hN : 4 ≤ N)
    (hbd : b + d < truncatedSixthLowerC δ) :
    (4 * logarithmicIntegral N * wuSingularSeries N /
      ((truncatedSixthLowerC δ - a - c) * log N)) *
      (∑ p ∈ truncatedSixthClosurePairs N a b c d, 1 / ((p.1 : ℝ) * p.2)) ≤
    ∑ p ∈ truncatedSixthClosurePairs N a b c d, truncatedSixthLowerClassicalTheta N δ p := by
  have hN1 : 1 < N := by omega
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hli : 0 ≤ logarithmicIntegral N :=
    (show (0 : ℝ) ≤ N / (2 * log N) by positivity).trans (box_trueLi_lower hN)
  have hC := wuSingularSeries_pos N (by omega)
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨hp1, hp2⟩ := mem_product.mp hp
  have hp' := mem_primeWindow.mp hp1
  have hq' := mem_primeWindow.mp hp2
  have hp0 : (0 : ℝ) < p.1 := by exact_mod_cast hp'.1.pos
  have hq0 : (0 : ℝ) < p.2 := by exact_mod_cast hq'.1.pos
  have he0 : 0 < p.1 * p.2 := mul_pos hp'.1.pos hq'.1.pos
  have heR : (0 : ℝ) < (p.1 * p.2 : ℕ) := by exact_mod_cast he0
  have hlo : (N : ℝ) ^ (a + c) ≤ (p.1 * p.2 : ℕ) := by
    rw [Nat.cast_mul, rpow_add hN0]
    exact mul_le_mul hp'.2.2.1 hq'.2.2.1 (rpow_nonneg hN0.le _) hp0.le
  have hup : (p.1 * p.2 : ℕ) < (N : ℝ) ^ truncatedSixthLowerC δ := by
    have hprod : (p.1 * p.2 : ℕ) ≤ (N : ℝ) ^ (b + d) := by
      rw [Nat.cast_mul, rpow_add hN0]
      exact mul_le_mul hp'.2.2.2.le hq'.2.2.2.le hq0.le (rpow_nonneg hN0.le _)
    apply hprod.trans_lt (rpow_lt_rpow_of_exponent_lt hNR ?_)
    exact hbd
  have hlpos : 0 < log ((N : ℝ) ^ truncatedSixthLowerC δ / (p.1 * p.2 : ℕ)) :=
    log_pos ((one_lt_div heR).mpr hup)
  have hlup : log ((N : ℝ) ^ truncatedSixthLowerC δ / (p.1 * p.2 : ℕ)) ≤
      (truncatedSixthLowerC δ - a - c) * log N := by
    have hlogprod := log_le_log (rpow_pos_of_pos hN0 _) hlo
    rw [log_rpow hN0] at hlogprod
    rw [log_div (rpow_pos_of_pos hN0 _).ne' heR.ne', log_rpow hN0]
    nlinarith
  have htpos : (0 : ℝ) < Nat.totient (p.1 * p.2) := by exact_mod_cast Nat.totient_pos.mpr he0
  have htot : (Nat.totient (p.1 * p.2) : ℝ) ≤ (p.1 * p.2 : ℕ) := by
    exact_mod_cast Nat.totient_le (p.1 * p.2)
  calc
    _ = 4 * logarithmicIntegral N * wuSingularSeries N /
      ((p.1 * p.2 : ℕ) * ((truncatedSixthLowerC δ - a - c) * log N)) := by
        push_cast
        simp only [div_eq_mul_inv, mul_inv]
        ring
    _ ≤ _ := by
      unfold truncatedSixthLowerClassicalTheta
      gcongr

theorem fifthPair_cell_theta_sharp {δ a b c d ε : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (ha0 : 0 < a) (hc0 : 0 < c)
    (hbd : b + d < truncatedSixthLowerC δ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (truncatedSixthMassRectangleCoefficient δ a b c d - ε) * truncatedSixthMassScale N ≤
        ∑ p ∈ truncatedSixthClosurePairs N a b c d, truncatedSixthLowerClassicalTheta N δ p := by
  have hL1 := log_nonneg ((one_le_div ha0).mpr hab)
  have hL2 := log_nonneg ((one_le_div hc0).mpr hcd)
  have hD : 0 < truncatedSixthLowerC δ - a - c := by
    linarith
  let K := truncatedSixthMassRectangleCoefficient δ a b c d
  have hK : 0 ≤ K := by dsimp [K, truncatedSixthMassRectangleCoefficient]; positivity
  let τ := ε / (4 * (K + 1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτeq : τ * (4 * (K + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hKτ : K * τ < ε / 2 := by nlinarith
  have hrat : K - ε / 2 < K / (1 + τ) := by
    apply (lt_div_iff₀ (by positivity : 0 < 1 + τ)).mpr
    nlinarith
  obtain ⟨T, hT4, hli⟩ := omega3X_trueLi_sharp_lower hτ
  have hmass := (truncatedSixthMass_rectangle_tendsto ha0 hab hc0 hcd).const_mul
    (4 / ((1 + τ) * (truncatedSixthLowerC δ - a - c)))
  have hlimit : 4 / ((1 + τ) * (truncatedSixthLowerC δ - a - c)) *
      (log (b / a) * log (d / c)) = K / (1 + τ) := by
    dsimp [K, truncatedSixthMassRectangleCoefficient]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hlimit] at hmass
  filter_upwards [hmass.eventually (lt_mem_nhds (show K - ε < K / (1 + τ) by linarith)),
    eventually_ge_atTop T] with N hm hN
  have hN4 := hT4.trans hN
  have hlog := log_pos (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_pos N (by omega)
  let P := ∑ p ∈ truncatedSixthClosurePairs N a b c d, 1 / ((p.1 : ℝ) * p.2)
  have hP : 0 ≤ P := sum_nonneg (fun _ _ => by positivity)
  have hscale : 0 ≤ truncatedSixthMassScale N := by unfold truncatedSixthMassScale; positivity
  change K - ε < 4 / ((1 + τ) * (truncatedSixthLowerC δ - a - c)) * P at hm
  calc
    _ ≤ (4 / ((1 + τ) * (truncatedSixthLowerC δ - a - c)) * P) * truncatedSixthMassScale N :=
      mul_le_mul_of_nonneg_right hm.le hscale
    _ = (4 * wuSingularSeries N / ((1 + τ) * (truncatedSixthLowerC δ - a - c) * log N) * P) *
        ((N : ℝ) / log N) := by
      dsimp [truncatedSixthMassScale]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ ≤ (4 * wuSingularSeries N / ((1 + τ) * (truncatedSixthLowerC δ - a - c) * log N) * P) *
        ((1 + τ) * logarithmicIntegral N) :=
      mul_le_mul_of_nonneg_left (hli N hN) (by positivity)
    _ = (4 * logarithmicIntegral N * wuSingularSeries N /
        ((truncatedSixthLowerC δ - a - c) * log N)) * P := by field_simp
    _ ≤ _ := fifthPair_cell_theta_lower hN4 hbd

end Wu2008DoubleSieve
