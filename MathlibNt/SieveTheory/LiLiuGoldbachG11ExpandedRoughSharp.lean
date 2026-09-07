import MathlibNt.SieveTheory.LiLiuGoldbachG11ExpandedOrdered
import MathlibNt.SieveTheory.LiLiuGoldbachG11ExpandedRoughUniform
import MathlibNt.SieveTheory.LiLiuBuchstabSharpClosure

open Finset LiLiuPrereqBuchstab
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11ExpandedOrdered_cofactor_geometry {N : ℕ} (hN : 4 ≤ N) {ρ : ℝ}
    (hρ : 1 ≤ ρ) (hρu : ρ ≤ 5/4) {v : GoldbachG11Label}
    (hv : v ∈ goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))) :
    let y := ρ^2*N/goldbachG11LabelProd v
    (N : ℝ)^(1/2 : ℝ) ≤ y ∧ y ≤ (N : ℝ)^2 ∧
      (N : ℝ)^(4/53 : ℝ) ≤ (v.2.2.2 : ℝ) ∧ (v.2.2.2 : ℝ) ≤ (N : ℝ)^(4/33 : ℝ) ∧
      (17/4 : ℝ) ≤ Real.log y/Real.log (v.2.2.2 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd0 : (0 : ℝ) < goldbachG11LabelProd v := by exact_mod_cast goldbachG11LabelProd_pos hv
  have hd1 : (1 : ℝ) ≤ goldbachG11LabelProd v := by exact_mod_cast goldbachG11LabelProd_pos hv
  have hρ1 : 1 ≤ ρ^2 := by nlinarith
  have hρ2 : ρ^2 ≤ (2 : ℝ) := by nlinarith
  have hx : (N : ℝ)/goldbachG11LabelProd v ≤ ρ^2*N/goldbachG11LabelProd v :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_left hn0.le hρ1) hd0.le
  have hxpos : (0 : ℝ) < (N : ℝ)/goldbachG11LabelProd v := div_pos hn0 hd0
  have hlower := goldbachG11_canonical_cofactor_lower_bound (by omega : 2 ≤ N) hv
  have hgeo := goldbachG11PrimeKernel_logGeometry hN hv
  have hyN : ρ^2*N/goldbachG11LabelProd v ≤ (N : ℝ)^2 := by
    calc
      _ ≤ ρ^2*N := div_le_self (by positivity) hd1
      _ ≤ 2*(N : ℝ) := mul_le_mul_of_nonneg_right hρ2 hn0.le
      _ ≤ _ := by
        have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
        nlinarith
  have hlog := Real.log_le_log hxpos hx
  have hu := div_le_div_of_nonneg_right hlog hgeo.2.1.le
  refine ⟨(Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/2 : ℝ) ≤ 17/33)).trans (hlower.trans hx),hyN,?_,?_,hgeo.2.2.1.trans hu⟩
  · obtain ⟨_hr,_hq,_hs,_ht,_hcop,hzr,hrq,_⟩ := mem_goldbachG11Labels_iff.mp hv
    exact hzr.trans (by exact_mod_cast hrq)
  · obtain ⟨_hr,_hq,_hs,_ht,_hcop,_hzr,_hrq,hqs,hst,htb⟩ := mem_goldbachG11Labels_iff.mp hv
    exact (show (v.2.2.2 : ℝ) ≤ v.1 from by exact_mod_cast hqs.trans hst).trans htb

/-- Weighted original labelled mother, with its enlarged product endpoint,
consumes the already proved sharp omega constant on its unchanged valid domain. -/
theorem goldbachG11ExpandedRoughMass_le_sharpKernel (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ρ : ℝ, 1 ≤ ρ → ρ ≤ 5/4 →
      ∀ h : ℝ → ℝ, (∀ r, 0 ≤ h r) →
      (Real.log (N : ℝ)/N)*goldbachG11ExpandedRoughMass N ρ h ≤
        ρ^2*((561522/1000000 : ℝ)+η)*goldbachG11PrimeKernel h N := by
  obtain ⟨M,hM,hm⟩ := goldbachG11_expanded_rough_uniform η hη
  refine ⟨M,hM,?_⟩
  intro N hN ρ hρ hρu h hh
  have hn4 := hM.trans hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold goldbachG11ExpandedRoughMass goldbachG11PrimeKernel
  rw [mul_sum,mul_sum]
  apply sum_le_sum
  intro v hv
  obtain ⟨hyl,hyu,hql,hqu,hu⟩ := goldbachG11ExpandedOrdered_cofactor_geometry hn4 hρ hρu hv
  obtain ⟨hy,hq,_hu,he⟩ := hm N hN v.2.2.2 (ρ^2*N/goldbachG11LabelProd v) hql hqu hyl hyu
  have hw := LiLiuBuchstabSharp.buchstab_sharp_tail_closed hu
  have hlq := Real.log_pos hq
  have hy0 : 0 ≤ ρ^2*N/goldbachG11LabelProd v := by linarith
  have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw hy0) hlq.le
  have hr : (roughCount (ρ^2*N/goldbachG11LabelProd v) v.2.2.2 : ℝ) ≤
      ((561522/1000000 : ℝ)+η)*(ρ^2*N/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ) := by
    have he' := (abs_le.mp he).2
    unfold goldbachG11BuchstabMass at he'
    have hid : ((561522/1000000 : ℝ)+η)*(ρ^2*N/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ) =
        (ρ^2*N/goldbachG11LabelProd v)*(561522/1000000)/Real.log (v.2.2.2 : ℝ)+
        η*(ρ^2*N/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ) := by ring
    rw [hid]
    linarith
  calc
    _ ≤ (Real.log (N : ℝ)/N)*(h (Real.log (v.2.2.1 : ℝ)/Real.log (N : ℝ))*
        (((561522/1000000 : ℝ)+η)*(ρ^2*N/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (hh _)) (div_nonneg hln.le hn0.le)
    _ = _ := by field_simp

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig