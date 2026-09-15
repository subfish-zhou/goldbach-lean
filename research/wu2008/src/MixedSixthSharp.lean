import MixedSixthTheta

namespace MixedSixth
open Finset Real Wu2008DoubleSieve Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

/-- No fixed loss in the high rectangle theta normalization. The elementary
Li lower bound contributes 1-2/N, which tends to one. -/
theorem rectangle_theta_sharp {δ a b c d ε : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (hcd : c ≤ d)
    (ha : truncatedSixthLowerAlpha ≤ a) (hc : truncatedSixthLowerBeta ≤ c)
    (hr : truncatedSixthLowerRegion δ b d) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (truncatedSixthMassRectangleCoefficient δ a b c d-ε)*truncatedSixthMassScale N ≤
        rectangleTheta N δ a b c d := by
  let D := truncatedSixthLowerC δ-a-c
  have hD : 0 < D := by
    have h := truncatedSixthLower_parameters.1
    dsimp [D]
    linarith [hr.2.2.2.2]
  have hp := truncatedSixthMass_packing_reciprocal_tendsto
    (truncatedSixthLower_parameters.1.trans_le ha) hab
    ((truncatedSixthLower_parameters.1.trans truncatedSixthLower_parameters.2.1).trans_le hc) hcd
  have hsmall : Tendsto (fun N : ℕ => (2:ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => (4/D)*truncatedSixthMassPackingReciprocal N a b c d*
      (1-2/(N:ℝ))) atTop (𝓝 (truncatedSixthMassRectangleCoefficient δ a b c d)) := by
    have h := (hp.const_mul (4/D)).mul ((tendsto_const_nhds (x := (1:ℝ))).sub hsmall)
    convert h using 1
    simp [truncatedSixthMassRectangleCoefficient,D]
    ring
  filter_upwards [hlim.eventually_const_lt (sub_lt_self _ hε),eventually_ge_atTop (4:ℕ)] with N hmass hN
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := (wuSingularSeries_pos N (show 0 < N by omega)).le
  have hP : 0 ≤ truncatedSixthMassPackingReciprocal N a b c d :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => by positivity))
  have hli := box_trueLi_sub_lower (le_refl (2:ℝ))
    (show (2:ℝ) ≤ N by exact_mod_cast (show 2 ≤ N by omega))
  have htwo : logarithmicIntegral 2 = 0 := by
    simp [logarithmicIntegral,MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral]
  rw [htwo,sub_zero] at hli
  have hscaled := mul_le_mul_of_nonneg_left hli
    (show 0 ≤ 4*wuSingularSeries N/(D*log N)*truncatedSixthMassPackingReciprocal N a b c d by positivity)
  have heq : ((4/D)*truncatedSixthMassPackingReciprocal N a b c d*(1-2/(N:ℝ)))*
      truncatedSixthMassScale N =
      (4*wuSingularSeries N/(D*log N)*truncatedSixthMassPackingReciprocal N a b c d)*
        (((N:ℝ)-2)/log N) := by
    unfold truncatedSixthMassScale
    field_simp
  have heq' : (4*wuSingularSeries N/(D*log N)*truncatedSixthMassPackingReciprocal N a b c d)*
      logarithmicIntegral N =
      (4*logarithmicIntegral N*wuSingularSeries N/((truncatedSixthLowerC δ-a-c)*log N))*
        truncatedSixthMassPackingReciprocal N a b c d := by dsimp [D]; ring
  exact (mul_le_mul_of_nonneg_right hmass.le (truncatedSixthClosure_scale_nonneg hN)).trans
    (heq.le.trans (hscaled.trans (heq'.le.trans (rectangle_theta_lower hN hδ hab hcd ha hc hr))))

/-- Exact scalar coefficient attached to each actual high coarse rectangle. -/
def highCoefficient (δ : ℝ) (n i : ℕ) : ℝ :=
  let s := truncatedSixthLowerS δ (hiX n i) (hiY n i)
  log (s-1)+(1/10000)*log (2/(s-1))

theorem highCoefficient_pos {δ : ℝ} (hδ : 0 ≤ δ) {n i : ℕ}
    (hi : i ∈ highCells δ n) : 0 < highCoefficient δ n i := by
  have hg := high_geometry hi
  have hy := hg.2.1.trans_lt (truncatedSixthClosure_lo_lt_hi n (coarse i).2)
  have hs := HighConsumer.high_source_bounds hδ hg.2.2 hy
  have hlog := log_nonneg (show 1 ≤ truncatedSixthLowerS δ (hiX n i) (hiY n i)-1 by linarith [hs.1])
  have hcor := PositiveH.lowerCorrection_pos
    (show 1 < truncatedSixthLowerS δ (hiX n i) (hiY n i) by linarith [hs.1])
    (show truncatedSixthLowerS δ (hiX n i) (hiY n i) < 3 by linarith [hs.2])
  unfold highCoefficient
  dsimp
  unfold PositiveH.lowerCorrection at hcor
  linarith only [hlog,hcor]

end
end MixedSixth
