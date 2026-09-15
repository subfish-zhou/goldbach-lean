import Wu08FourMainNormalized

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace Wu08FirstPrimeFour.Normalization

/-- A polynomial parameter loss, hence tending to zero without any quantitative
search, table, new logarithmic approximation or Taylor order. -/
def normalizationLoss (C t : ℝ) : ℝ :=
  ((1+t)^2-1)*8+(1+t)^2*(32*t+4*exp (-eulerMascheroniConstant)*C*t+t)

theorem normalizationLoss_small (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < 1/8 ∧ normalizationLoss C t < ε := by
  have ht : Tendsto (normalizationLoss C) (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (normalizationLoss C) 0 := by unfold normalizationLoss; fun_prop
    simpa only [normalizationLoss,add_zero,one_pow,sub_self,zero_mul,mul_zero,zero_add] using hc.tendsto
  obtain ⟨r,hr,hnear⟩ := Metric.tendsto_nhds_nhds.mp ht ε hε
  obtain ⟨t,ht0,htu⟩ := exists_between (lt_min hr (by norm_num : (0 : ℝ) < 1/8))
  have htr : t < r := htu.trans_le (min_le_left _ _)
  have hclose := hnear (show dist t (0 : ℝ) < r by simpa only [Real.dist_eq,sub_zero,abs_of_pos ht0] using htr)
  refine ⟨t,ht0,htu.trans_le (min_le_right _ _),?_⟩
  have hh : |normalizationLoss C t| < ε := by simpa only [Real.dist_eq,sub_zero] using hclose
  exact (abs_lt.mp hh).2

/-- The actual masses of all the original occupied cells, not an arbitrary
family mass assumption. -/
theorem gridMass_weight_le_eight {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hN : (4 : ℝ) ≤ N) (hξ : 0 < ξ) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hbig : 4 ≤ (N : ℝ)^truncatedSixthLowerAlpha/2) :
    0 ≤ plainGridMass N e ξ ρ ∧ weightedGridMass N e ξ ρ ≤ 8*plainGridMass N e ξ ρ := by
  refine ⟨sum_nonneg (fun k _ => cellMass_nonneg _ _ _ _ k),?_⟩
  unfold weightedGridMass plainGridMass
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  obtain ⟨_,_,_,hTl,hTu⟩ := occupied_geometry hξ hρ hρu hk
  have hT : 1 ≤ (2/3 : ℝ)*ρ^k.1 := by linarith
  obtain ⟨hx,hxu,_⟩ := level_log_geometry (δ := 0) hN hT hTu
  exact mul_le_mul_of_nonneg_right (cellWeight_bounds hx hxu).2 (cellMass_nonneg _ _ _ _ _)

/-- Every epsilon selects genuine positive delta,eta before ONE N threshold
for BOTH properMain terms and every permitted grid. Only the weighted-grid to
fourfold-Buchstab integral bridge remains; no 'correct density' hypothesis. -/
theorem properMain_epsilon_normalized {ε : ℝ} (hε : 0 < ε) :
    ∃ δ η : ℝ, 0 < δ ∧ δ < 1/4 ∧ 0 < η ∧ η < 1/8 ∧
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
    ∀ e : Bool, ∀ ξ ρ : ℝ, 0 < ξ → 1 < ρ → ρ ≤ 5/4 →
      properMain N e ξ ρ δ η ≤ (wuSingularSeries N/log N)*
        (weightedGridMass N e ξ ρ+ε*plainGridMass N e ξ ρ) := by
  obtain ⟨C,_,hc⟩ := properMain_weighted_upper
  obtain ⟨t,ht,htu,hsmall⟩ := normalizationLoss_small C hε
  have htu4 : t < 1/4 := by linarith
  obtain ⟨Nm,hm⟩ := hc t t t ht.le htu4 ht htu ht
  obtain ⟨Ng,hg⟩ := occupied_level_gate ht.le htu4 ht 4
  obtain ⟨Nb,hb⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 8 0 truncatedSixthLowerAlpha
      (by norm_num [truncatedSixthLowerAlpha]))
  refine ⟨t,t,ht,htu4,ht,htu,max 4 (max Nm (max Ng Nb)),?_⟩
  intro N hN hEven e ξ ρ hξ hρ hρu
  have hn4 : (4 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hNm := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hbig : 4 ≤ (N : ℝ)^truncatedSixthLowerAlpha/2 := by
    have hh : (8 : ℝ) ≤ (N : ℝ)^truncatedSixthLowerAlpha := by simpa using hb N hNb
    linarith
  obtain ⟨hp,hw⟩ := gridMass_weight_le_eight hn4 hξ hρ hρu hbig
  have hs : 0 ≤ wuSingularSeries N/log N := by
    rw [wuSingularSeries_eq_liu N (by exact_mod_cast (show (0 : ℝ) < N by linarith))]
    exact div_nonneg (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le
      (log_nonneg (by linarith))
  have hsq : 0 ≤ (1+t)^2-1 := by nlinarith
  let E := 32*t+4*exp (-eulerMascheroniConstant)*C*t+t
  have hpay : (1+t)^2*(weightedGridMass N e ξ ρ+E*plainGridMass N e ξ ρ) ≤
      weightedGridMass N e ξ ρ+ε*plainGridMass N e ξ ρ := by
    calc
      _ = weightedGridMass N e ξ ρ+((1+t)^2-1)*weightedGridMass N e ξ ρ+
          (1+t)^2*E*plainGridMass N e ξ ρ := by ring
      _ ≤ weightedGridMass N e ξ ρ+((1+t)^2-1)*(8*plainGridMass N e ξ ρ)+
          (1+t)^2*E*plainGridMass N e ξ ρ := by
        exact add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hw hsq)) (le_refl _)
      _ = weightedGridMass N e ξ ρ+normalizationLoss C t*plainGridMass N e ξ ρ := by
        unfold normalizationLoss E
        ring
      _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hsmall.le hp)
  calc
    _ ≤ (1+t)^2*(wuSingularSeries N/log N)*
        (weightedGridMass N e ξ ρ+E*plainGridMass N e ξ ρ) := hm N hNm hEven e ξ ρ hξ hρ hρu
    _ = (wuSingularSeries N/log N)*
        ((1+t)^2*(weightedGridMass N e ξ ρ+E*plainGridMass N e ξ ρ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpay hs

#print axioms properMain_epsilon_normalized
end Wu08FirstPrimeFour.Normalization
