import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassPacking

/-!
# Sharp lower mass of the constructed rectangle packing

The sharp true-Li lower normalization is the existing producer.
The resulting coefficient is independent of N and the packing loses
no fixed fraction of the reciprocal-prime rectangle mass.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def truncatedSixthMassScale (N : ℕ) : ℝ :=
  wuSingularSeries N * N / log N ^ (2 : ℕ)

noncomputable def truncatedSixthMassRectangleCoefficient (δ a b c d : ℝ) : ℝ :=
  4 * (log (b / a) * log (d / c)) / (truncatedSixthLowerC δ - a - c)

theorem truncatedSixthMass_packing_theta_sharp {δ a b c d ε : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (ha : truncatedSixthLowerAlpha ≤ a) (hc : truncatedSixthLowerBeta ≤ c)
    (hbd : truncatedSixthLowerAdmissibleRegion δ b d) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (truncatedSixthMassRectangleCoefficient δ a b c d - ε) * truncatedSixthMassScale N ≤
        truncatedSixthMassPackingTheta N δ a b c d := by
  have ha0 := truncatedSixthLower_parameters.1.trans_le ha
  have hc0 := (truncatedSixthLower_parameters.1.trans
    truncatedSixthLower_parameters.2.1).trans_le hc
  have hL1 : 0 ≤ log (b / a) := log_nonneg ((one_le_div ha0).mpr hab)
  have hL2 : 0 ≤ log (d / c) := log_nonneg ((one_le_div hc0).mpr hcd)
  have hD : 0 < truncatedSixthLowerC δ - a - c := by
    have hα := truncatedSixthLower_parameters.1
    linarith [hbd.1.2.2.2.2]
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
  have hmass := (truncatedSixthMass_packing_reciprocal_tendsto ha0 hab hc0 hcd).const_mul
    (4 / ((1 + τ) * (truncatedSixthLowerC δ - a - c)))
  have hlimit : 4 / ((1 + τ) * (truncatedSixthLowerC δ - a - c)) *
      (log (b / a) * log (d / c)) = K / (1 + τ) := by
    dsimp [K, truncatedSixthMassRectangleCoefficient]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hlimit] at hmass
  have he := hmass.eventually (lt_mem_nhds (show K - ε < K / (1 + τ) by linarith))
  filter_upwards [he, eventually_ge_atTop T] with N hm hN
  have hN4 := hT4.trans hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_pos N (by omega)
  have hR : 0 ≤ truncatedSixthMassPackingReciprocal N a b c d := by
    unfold truncatedSixthMassPackingReciprocal
    exact sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => by positivity))
  have hscale : 0 ≤ truncatedSixthMassScale N := by
    unfold truncatedSixthMassScale
    positivity
  change K - ε < 4 / ((1 + τ) * (truncatedSixthLowerC δ - a - c)) *
    truncatedSixthMassPackingReciprocal N a b c d at hm
  calc
    _ ≤ (4 / ((1 + τ) * (truncatedSixthLowerC δ - a - c)) *
        truncatedSixthMassPackingReciprocal N a b c d) * truncatedSixthMassScale N :=
      mul_le_mul_of_nonneg_right hm.le hscale
    _ = (4 * wuSingularSeries N /
        ((1 + τ) * (truncatedSixthLowerC δ - a - c) * log N) *
        truncatedSixthMassPackingReciprocal N a b c d) * ((N : ℝ) / log N) := by
      dsimp [truncatedSixthMassScale]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ ≤ (4 * wuSingularSeries N /
        ((1 + τ) * (truncatedSixthLowerC δ - a - c) * log N) *
        truncatedSixthMassPackingReciprocal N a b c d) * ((1 + τ) * logarithmicIntegral N) :=
      mul_le_mul_of_nonneg_left (hli N hN) (by positivity)
    _ = (4 * logarithmicIntegral N * wuSingularSeries N /
        ((truncatedSixthLowerC δ - a - c) * log N)) *
        truncatedSixthMassPackingReciprocal N a b c d := by field_simp
    _ ≤ _ := truncatedSixthMass_packing_theta_lower hN4 hab hcd ha hc hbd

theorem truncatedSixthMass_packing_grid_parameter {N : ℕ} {δ a b c d s : ℝ}
    (hN : 1 < N) (hab : a ≤ b) (hcd : c ≤ d)
    (hs : s ≤ truncatedSixthLowerS δ b d)
    {j : ℕ × ℕ} (hj : j ∈ truncatedSixthMassPacking N a b c d) :
    s ≤ truncatedSixthLowerS δ
      (truncatedSixthMassGridPoint N a (j.1 + 1))
      (truncatedSixthMassGridPoint N c (j.2 + 1)) := by
  obtain ⟨hj1, hj2⟩ := mem_product.mp hj
  have hx := (truncatedSixthMass_grid_point_bounds hN hab (mem_range.mp hj1)).2
  have hy := (truncatedSixthMass_grid_point_bounds hN hcd (mem_range.mp hj2)).2
  apply hs.trans
  unfold truncatedSixthLowerS
  exact div_le_div_of_nonneg_right (by linarith) truncatedSixthLower_parameters.1.le

theorem truncatedSixthMass_packing_gain_count {δ η a b c d s : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hη : 0 < η)
    (hab : a ≤ b) (hcd : c ≤ d)
    (ha : truncatedSixthLowerAlpha ≤ a) (hc : truncatedSixthLowerBeta ≤ c)
    (hbd : truncatedSixthLowerAdmissibleRegion δ b d)
    (hs2 : 2 ≤ s) (hs5 : s ≤ 5) (hs : s ≤ truncatedSixthLowerS δ b d) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (wuLowerCoefficient s + wuImprovementLimit false δ s - η) *
        truncatedSixthMassPackingTheta N δ a b c d ≤
        ∑ j ∈ truncatedSixthMassPacking N a b c d,
          ∑ p ∈ truncatedSixthMassPackingBox N a c j,
            (sieveCount N (p.1 * p.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨T, hT, hgain⟩ := truncatedSixthLower_finite_grid_gain hδ hδhi hη {s}
    (by intro t ht; simpa using Finset.mem_singleton.mp ht ▸ And.intro hs2 hs5)
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hN4 := hT.trans hN
  have hN1 : 1 < N := by omega
  unfold truncatedSixthMassPackingTheta
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  have hg := truncatedSixthMass_packing_admissible hN1 hab hcd ha hc hbd hj
  have hqlo : (N : ℝ) ^ truncatedSixthLowerAlpha ≤
      (N : ℝ) ^ truncatedSixthMassGridPoint N c (j.2 + 1) / truncatedSixthMassDelta N :=
    (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1.le)
      truncatedSixthLower_parameters.2.1.le).trans hg.2.2
  have h := hgain N hN he (truncatedSixthMassDelta N)
    (truncatedSixthMassGridPoint N a (j.1 + 1))
    (truncatedSixthMassGridPoint N c (j.2 + 1))
    (truncatedSixthMass_delta_legal hN1).2.1 (truncatedSixthMass_delta_legal hN1).2.2
    hg.1 hg.2.1 hqlo s (Finset.mem_singleton_self s)
    (truncatedSixthMass_packing_grid_parameter hN1 hab hcd hs hj)
  change _ ≤ _ at h
  apply h.trans_eq
  dsimp [truncatedSixthMassPackingBox, truncatedSixthLowerBoxPairs]
  rw [sum_product, sum_product, sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  rw [mul_comm p q]

end Wu2008DoubleSieve
