import Wu08RecoverySmallTerminal

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace Wu08FirstPrimeFour.SmallBoundaryRecovery
open Normalization SmallGrid

/-- A genuine arbitrary upper bound on delta, selected in the explicit
normalization coefficient. No monotonicity of properMain, H, or h is assumed. -/
theorem properMain_normalized_below {ε dmax : ℝ} (hε : 0 < ε) (hmax : 0 < dmax) :
    ∃ δ η : ℝ, 0 < δ ∧ δ < dmax ∧ δ < 1/4 ∧ 0 < η ∧ η < 1/8 ∧
      ∃ T : ℝ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ (N : ℝ) → Even N →
        ∀ e : Bool, ∀ ξ ρ : ℝ, 0 < ξ → 1 < ρ → ρ ≤ 5/4 →
          properMain N e ξ ρ δ η ≤ (wuSingularSeries N/log N)*
            (weightedGridMass N e ξ ρ+ε*plainGridMass N e ξ ρ) := by
  obtain ⟨C,_,hc⟩ := properMain_weighted_upper
  obtain ⟨t,ht,htu,hsmall⟩ := normalizationLoss_small C hε
  let δ := min t (dmax/2)
  have hδ : 0 < δ := lt_min ht (by positivity)
  have hδt : δ ≤ t := min_le_left _ _
  have hδm : δ < dmax := (min_le_right _ _).trans_lt (by linarith)
  have hδu : δ < 1/4 := by linarith
  obtain ⟨Tm,hm⟩ := hc δ t t hδ.le hδu ht htu ht
  obtain ⟨Tb,hb⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 8 0 truncatedSixthLowerAlpha
      (by norm_num [truncatedSixthLowerAlpha]))
  refine ⟨δ,t,hδ,hδm,hδu,ht,htu,max 4 (max Tm Tb),le_max_left _ _,?_⟩
  intro N hN he e ξ ρ hξ hρ hρu
  have hn4 : (4 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hNm := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hbig : 4 ≤ (N : ℝ)^truncatedSixthLowerAlpha/2 := by
    have hh : (8 : ℝ) ≤ (N : ℝ)^truncatedSixthLowerAlpha := by simpa using hb N hNb
    linarith
  obtain ⟨hp,hw⟩ := gridMass_weight_le_eight hn4 hξ hρ hρu hbig
  have hs : 0 ≤ wuSingularSeries N/log N := by
    rw [wuSingularSeries_eq_liu N (by exact_mod_cast (show (0 : ℝ) < N by linarith))]
    exact div_nonneg (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le
      (log_nonneg (by linarith))
  have hsq : 0 ≤ (1+t)^2-1 := by nlinarith
  let E := 32*δ+4*exp (-eulerMascheroniConstant)*C*t+t
  let F := 32*t+4*exp (-eulerMascheroniConstant)*C*t+t
  have hEF : E ≤ F := by dsimp [E,F]; linarith only [hδt]
  have hpay : (1+t)^2*(weightedGridMass N e ξ ρ+E*plainGridMass N e ξ ρ) ≤
      weightedGridMass N e ξ ρ+ε*plainGridMass N e ξ ρ := by
    calc
      _ ≤ (1+t)^2*(weightedGridMass N e ξ ρ+F*plainGridMass N e ξ ρ) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hEF hp)) (sq_nonneg _)
      _ = weightedGridMass N e ξ ρ+((1+t)^2-1)*weightedGridMass N e ξ ρ+
          (1+t)^2*F*plainGridMass N e ξ ρ := by ring
      _ ≤ weightedGridMass N e ξ ρ+((1+t)^2-1)*(8*plainGridMass N e ξ ρ)+
          (1+t)^2*F*plainGridMass N e ξ ρ :=
        add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hw hsq)) (le_refl _)
      _ = weightedGridMass N e ξ ρ+normalizationLoss C t*plainGridMass N e ξ ρ := by
        unfold normalizationLoss F
        ring
      _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hsmall.le hp)
  calc
    _ ≤ (1+t)^2*(wuSingularSeries N/log N)*
        (weightedGridMass N e ξ ρ+E*plainGridMass N e ξ ρ) := hm N hNm he e ξ ρ hξ hρ hρu
    _ = (wuSingularSeries N/log N)*
        ((1+t)^2*(weightedGridMass N e ξ ρ+E*plainGridMass N e ξ ρ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpay hs

/-- Capped counterpart of the frozen actual Buchstab producer. -/
theorem properMain_buchstab_below {ε τ dmax : ℝ} (hε : 0 < ε) (hτ : 0 < τ) (hmax : 0 < dmax) :
    ∃ δ η : ℝ, 0 < δ ∧ δ < dmax ∧ δ < 1/4 ∧ 0 < η ∧ η < 1/8 ∧
      ∃ T : ℝ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ (N : ℝ) → Even N →
        ∀ e : Bool, ∀ ξ ρ : ℝ, 0 < ξ → 1 < ρ → ρ ≤ 5/4 →
          properMain N e ξ ρ δ η ≤
            (wuSingularSeries N*N/log N^2)*(ρ*buchstabGrid N e ρ ε τ) := by
  obtain ⟨δ,η,hδ,hδm,hδu,hη,hηu,Tp,hTp,hp⟩ := properMain_normalized_below hε hmax
  obtain ⟨Tg,_,hg⟩ := actualGrid_buchstab hτ
  refine ⟨δ,η,hδ,hδm,hδu,hη,hηu,max Tp Tg,hTp.trans (le_max_left _ _),?_⟩
  intro N hN he e ξ ρ hξ hρ hρu
  have hNp := (le_max_left _ _).trans hN
  have hn4 := hTp.trans hNp
  have hs : 0 ≤ wuSingularSeries N/log N := by
    rw [wuSingularSeries_eq_liu N (by exact_mod_cast (show (0 : ℝ) < N by linarith))]
    exact div_nonneg (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le
      (log_nonneg (by linarith))
  have hh := hg N ((le_max_right _ _).trans hN) e ξ ρ ε hξ hρ hρu hε.le
  exact (hp N hNp he e ξ ρ hξ hρ hρu).trans
    ((mul_le_mul_of_nonneg_left hh hs).trans_eq (by ring))

theorem properMain_integral_below {σ dmax : ℝ} (hσ : 0 < σ) (hmax : 0 < dmax) :
    ∃ δ η ρ : ℝ, 0 < δ ∧ δ < dmax ∧ δ < 1/4 ∧ 0 < η ∧ η < 1/8 ∧ 1 < ρ ∧ ρ ≤ 5/4 ∧
      ∃ T : ℝ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ (N : ℝ) → Even N →
        ∀ e : Bool, ∀ ξ : ℝ, 0 < ξ →
          properMain N e ξ ρ δ η ≤
            (SmallQuadrature.I e+σ)*(wuSingularSeries N*N/log N^2) := by
  obtain ⟨ε,τ,hε,_,hτ,Tg,hTg,hg⟩ := buchstabGrid_integral_paid (show 0 < σ/4 by positivity)
  obtain ⟨δ,η,hδ,hδm,hδu,hη,hηu,Tp,_,hp⟩ := properMain_buchstab_below hε hτ hmax
  obtain ⟨ρ,hρ,hρu,hr⟩ := choose_dilation hσ
  refine ⟨δ,η,ρ,hδ,hδm,hδu,hη,hηu,hρ,hρu,max Tg Tp,hTg.trans (le_max_left _ _),?_⟩
  intro N hN he e ξ hξ
  have hNg := (le_max_left _ _).trans hN
  have hn4 := hTg.trans hNg
  have hs : 0 ≤ wuSingularSeries N*N/log N^2 := by
    rw [wuSingularSeries_eq_liu N (by exact_mod_cast (show (0 : ℝ) < N by linarith))]
    exact div_nonneg (mul_nonneg (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg _)) (sq_nonneg _)
  have hgrid := mul_le_mul_of_nonneg_left (hg N hNg e ρ hρ hρu) (by linarith : 0 ≤ ρ)
  have hh := hp N ((le_max_right _ _).trans hN) he e ξ ρ hξ hρ hρu
  exact hh.trans ((mul_le_mul_of_nonneg_left (hgrid.trans (hr e)) hs).trans_eq (mul_comm _ _))

#check properMain_normalized_below
#print axioms properMain_normalized_below
#check properMain_buchstab_below
#print axioms properMain_buchstab_below
#check properMain_integral_below
#print axioms properMain_integral_below
end Wu08FirstPrimeFour.SmallBoundaryRecovery
