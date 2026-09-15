import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassGrid
import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralNormalization

/-!
# Sufficient shrinking-box mass inside one coarse rectangle

The finite packing is explicitly constructed from the two inner grids.
The reciprocal mass tends to the full rectangle mass. No count or
main-mass hypothesis is supplied by a caller.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def truncatedSixthMassPacking (N : ℕ) (a b c d : ℝ) : Finset (ℕ × ℕ) :=
  range (truncatedSixthMassGridSize N a b) ×ˢ range (truncatedSixthMassGridSize N c d)

noncomputable def truncatedSixthMassPackingBox (N : ℕ) (a c : ℝ) (j : ℕ × ℕ) :
    Finset (ℕ × ℕ) :=
  truncatedSixthLowerBoxPairs N (truncatedSixthMassDelta N)
    (truncatedSixthMassGridPoint N a (j.1 + 1))
    (truncatedSixthMassGridPoint N c (j.2 + 1))

noncomputable def truncatedSixthMassPackingReciprocal (N : ℕ) (a b c d : ℝ) : ℝ :=
  ∑ j ∈ truncatedSixthMassPacking N a b c d,
    ∑ t ∈ truncatedSixthMassPackingBox N a c j, 1 / ((t.1 : ℝ) * t.2)

noncomputable def truncatedSixthMassPackingTheta (N : ℕ) (δ a b c d : ℝ) : ℝ :=
  ∑ j ∈ truncatedSixthMassPacking N a b c d,
    boxTheta N ((N : ℝ) ^ truncatedSixthLowerC δ)
      (convolutionWuWindows N (truncatedSixthMassDelta N)
        ![(N : ℝ) ^ truncatedSixthMassGridPoint N c (j.2 + 1),
          (N : ℝ) ^ truncatedSixthMassGridPoint N a (j.1 + 1)])

theorem truncatedSixthMass_packing_disjoint {N : ℕ} (hN : 1 < N) (a c : ℝ) :
    Pairwise (fun i j => Disjoint (truncatedSixthMassPackingBox N a c i)
      (truncatedSixthMassPackingBox N a c j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hi hj
  obtain ⟨hi1, hi2⟩ := mem_product.mp hi
  obtain ⟨hj1, hj2⟩ := mem_product.mp hj
  by_cases he : i.1 = j.1
  · have hne : i.2 ≠ j.2 := fun h => hij (Prod.ext he h)
    exact Finset.disjoint_left.mp (truncatedSixthMass_grid_disjoint hN c hne) hi2 hj2
  · exact Finset.disjoint_left.mp (truncatedSixthMass_grid_disjoint hN a he) hi1 hj1

theorem truncatedSixthMass_packing_reciprocal_eq {N : ℕ} (hN : 1 < N) (a b c d : ℝ) :
    truncatedSixthMassPackingReciprocal N a b c d =
      truncatedSixthMassPrimeSum N a (truncatedSixthMassTerminal N a b) *
        truncatedSixthMassPrimeSum N c (truncatedSixthMassTerminal N c d) := by
  unfold truncatedSixthMassPackingReciprocal truncatedSixthMassPacking
    truncatedSixthMassPackingBox truncatedSixthLowerBoxPairs truncatedSixthMassPrimeSum
  rw [truncatedSixthMass_grid_sum hN a b, truncatedSixthMass_grid_sum hN c d]
  simp only [sum_product, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  ring

theorem truncatedSixthMass_packing_reciprocal_tendsto {a b c d : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) :
    Tendsto (fun N => truncatedSixthMassPackingReciprocal N a b c d)
      atTop (𝓝 (log (b / a) * log (d / c))) := by
  apply ((truncatedSixthMass_trimmed_prime_tendsto ha hab).mul
    (truncatedSixthMass_trimmed_prime_tendsto hc hcd)).congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (truncatedSixthMass_packing_reciprocal_eq (by omega) a b c d).symm

theorem truncatedSixthMass_packing_admissible {N : ℕ} {δ a b c d : ℝ}
    (hN : 1 < N) (hab : a ≤ b) (hcd : c ≤ d)
    (ha : truncatedSixthLowerAlpha ≤ a) (hc : truncatedSixthLowerBeta ≤ c)
    (hbd : truncatedSixthLowerAdmissibleRegion δ b d)
    {j : ℕ × ℕ} (hj : j ∈ truncatedSixthMassPacking N a b c d) :
    truncatedSixthLowerAdmissibleRegion δ
        (truncatedSixthMassGridPoint N a (j.1 + 1))
        (truncatedSixthMassGridPoint N c (j.2 + 1)) ∧
      (N : ℝ) ^ truncatedSixthLowerAlpha ≤
        (N : ℝ) ^ truncatedSixthMassGridPoint N a (j.1 + 1) / truncatedSixthMassDelta N ∧
      (N : ℝ) ^ truncatedSixthLowerBeta ≤
        (N : ℝ) ^ truncatedSixthMassGridPoint N c (j.2 + 1) / truncatedSixthMassDelta N := by
  obtain ⟨hj1, hj2⟩ := mem_product.mp hj
  have hx := truncatedSixthMass_grid_point_bounds hN hab (mem_range.mp hj1)
  have hy := truncatedSixthMass_grid_point_bounds hN hcd (mem_range.mp hj2)
  have hmonoA := (truncatedSixthMass_grid_point_mono hN a).monotone (Nat.le_succ j.1)
  have hmonoC := (truncatedSixthMass_grid_point_mono hN c).monotone (Nat.le_succ j.2)
  refine ⟨⟨⟨ha.trans (hx.1.trans hmonoA), hx.2.trans hbd.1.2.1,
    hc.trans (hy.1.trans hmonoC), hy.2.trans hbd.1.2.2.2.1,
    (add_le_add hx.2 hy.2).trans hbd.1.2.2.2.2⟩, hy.2.trans hbd.2⟩, ?_, ?_⟩
  · rw [truncatedSixthMass_grid_lower_endpoint hN]
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) (ha.trans hx.1)
  · rw [truncatedSixthMass_grid_lower_endpoint hN]
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) (hc.trans hy.1)

theorem truncatedSixthMass_box_theta_lower {N : ℕ} {δ a c x y Δ : ℝ}
    (hN : 4 ≤ N)
    (hxy : truncatedSixthLowerAdmissibleRegion δ x y)
    (ha : (N : ℝ) ^ a ≤ (N : ℝ) ^ x / Δ)
    (hc : (N : ℝ) ^ c ≤ (N : ℝ) ^ y / Δ) :
    (4 * logarithmicIntegral N * wuSingularSeries N /
        ((truncatedSixthLowerC δ - a - c) * log N)) *
      (∑ p ∈ truncatedSixthLowerBoxPairs N Δ x y, 1 / ((p.1 : ℝ) * p.2)) ≤
      boxTheta N ((N : ℝ) ^ truncatedSixthLowerC δ)
        (convolutionWuWindows N Δ ![(N : ℝ) ^ y, (N : ℝ) ^ x]) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := log_pos hNR
  have hC := wuSingularSeries_pos N (by omega)
  have hli : 0 ≤ logarithmicIntegral N :=
    (show (0 : ℝ) ≤ N / (2 * log N) by positivity).trans (box_trueLi_lower hN)
  have hW : convolutionWuWindows N Δ ![(N : ℝ) ^ y, (N : ℝ) ^ x] =
      ![primeWindow N ((N : ℝ) ^ y / Δ) ((N : ℝ) ^ y),
        primeWindow N ((N : ℝ) ^ x / Δ) ((N : ℝ) ^ x)] := by
    funext j
    fin_cases j <;> rfl
  unfold boxTheta
  rw [hW]
  have hsum :
      wuSingularSeries N / ((truncatedSixthLowerC δ - a - c) * log N) *
        (∑ p ∈ truncatedSixthLowerBoxPairs N Δ x y, 1 / ((p.1 : ℝ) * p.2)) ≤
      ∑ e ∈ boxConvolutionSupport
        ![primeWindow N ((N : ℝ) ^ y / Δ) ((N : ℝ) ^ y),
          primeWindow N ((N : ℝ) ^ x / Δ) ((N : ℝ) ^ x)],
        (convolutionCoeff
          ![primeWindow N ((N : ℝ) ^ y / Δ) ((N : ℝ) ^ y),
            primeWindow N ((N : ℝ) ^ x / Δ) ((N : ℝ) ^ x)] e : ℝ) *
          (wuSingularSeries (e * N) / ((Nat.totient e : ℝ) *
            log ((N : ℝ) ^ truncatedSixthLowerC δ / e))) := by
    rw [truncatedSixthLower_two_window_sum]
    unfold truncatedSixthLowerBoxPairs
    rw [mul_sum, sum_product, sum_product, sum_comm]
    apply sum_le_sum
    intro q hq
    apply sum_le_sum
    intro p hp
    have hp' := mem_primeWindow.mp hp
    have hq' := mem_primeWindow.mp hq
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq'.1.pos
    have he0 : 0 < q * p := mul_pos hq'.1.pos hp'.1.pos
    have heR : (0 : ℝ) < (q * p : ℕ) := by exact_mod_cast he0
    have hlo : (N : ℝ) ^ (a + c) ≤ (q * p : ℕ) := by
      rw [Nat.cast_mul, rpow_add hN0, mul_comm (q : ℝ)]
      exact mul_le_mul (ha.trans hp'.2.2.1) (hc.trans hq'.2.2.1)
        (rpow_nonneg hN0.le _) hp0.le
    have hup : (q * p : ℕ) < (N : ℝ) ^ truncatedSixthLowerC δ := by
      have hprod : (q * p : ℕ) ≤ (N : ℝ) ^ (x + y) := by
        rw [Nat.cast_mul, rpow_add hN0, mul_comm (q : ℝ)]
        exact mul_le_mul hp'.2.2.2.le hq'.2.2.2.le hq0.le (rpow_nonneg hN0.le _)
      apply hprod.trans_lt (rpow_lt_rpow_of_exponent_lt hNR ?_)
      have hα := truncatedSixthLower_parameters.1
      linarith [hxy.1.2.2.2.2]
    have hlpos : 0 < log ((N : ℝ) ^ truncatedSixthLowerC δ / (q * p : ℕ)) :=
      log_pos ((one_lt_div heR).mpr hup)
    have hlup : log ((N : ℝ) ^ truncatedSixthLowerC δ / (q * p : ℕ)) ≤
        (truncatedSixthLowerC δ - a - c) * log N := by
      have hlogprod := log_le_log (rpow_pos_of_pos hN0 _) hlo
      rw [log_rpow hN0] at hlogprod
      rw [log_div (rpow_pos_of_pos hN0 _).ne' heR.ne', log_rpow hN0]
      nlinarith
    have htpos : (0 : ℝ) < Nat.totient (q * p) := by exact_mod_cast Nat.totient_pos.mpr he0
    have htot : (Nat.totient (q * p) : ℝ) ≤ (q * p : ℕ) := by exact_mod_cast Nat.totient_le (q * p)
    have hCmul := wuSingularSeries_le_mul (N := N) (d := q * p) (by omega) he0
    have hCmul0 : 0 ≤ wuSingularSeries (q * p * N) := (hC.trans_le hCmul).le
    calc
      _ = wuSingularSeries N / ((q * p : ℕ) *
          ((truncatedSixthLowerC δ - a - c) * log N)) := by
            push_cast
            simp only [div_eq_mul_inv, mul_inv]
            ring
      _ ≤ _ := by
        change _ ≤ wuSingularSeries (q * p * N) /
          ((Nat.totient (q * p) : ℝ) * log ((N : ℝ) ^ truncatedSixthLowerC δ / (q * p : ℕ)))
        gcongr
  have h := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hli)
  simpa only [div_eq_mul_inv, mul_assoc] using h

theorem truncatedSixthMass_packing_theta_lower {N : ℕ} {δ a b c d : ℝ}
    (hN : 4 ≤ N) (hab : a ≤ b) (hcd : c ≤ d)
    (ha : truncatedSixthLowerAlpha ≤ a) (hc : truncatedSixthLowerBeta ≤ c)
    (hbd : truncatedSixthLowerAdmissibleRegion δ b d) :
    (4 * logarithmicIntegral N * wuSingularSeries N /
      ((truncatedSixthLowerC δ - a - c) * log N)) *
        truncatedSixthMassPackingReciprocal N a b c d ≤
      truncatedSixthMassPackingTheta N δ a b c d := by
  unfold truncatedSixthMassPackingReciprocal truncatedSixthMassPackingTheta
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  have hgeom := truncatedSixthMass_packing_admissible (by omega) hab hcd ha hc hbd hj
  obtain ⟨hj1, hj2⟩ := mem_product.mp hj
  have hx := truncatedSixthMass_grid_point_bounds (by omega) hab (mem_range.mp hj1)
  have hy := truncatedSixthMass_grid_point_bounds (by omega) hcd (mem_range.mp hj2)
  apply truncatedSixthMass_box_theta_lower hN hgeom.1
  · rw [truncatedSixthMass_grid_lower_endpoint (by omega)]
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hx.1
  · rw [truncatedSixthMass_grid_lower_endpoint (by omega)]
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hy.1

end Wu2008DoubleSieve
