import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1028CommonMajorant
import Mathlib.Analysis.Calculus.Deriv.Inverse

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace Section10CanonicalXi

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The canonical function `η(x)=∫₀¹ exp(tx)dt`, including its removable value at zero. -/
noncomputable def eta (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, Real.exp (t * x)

lemma eta_eq_div {x : ℝ} (hx : x ≠ 0) : eta x = (Real.exp x - 1) / x := by
  rw [eta]
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => Real.exp (u * x) / x) (Real.exp (t * x)) t := by
    intro t _
    have h := ((hasDerivAt_id t).mul_const x).exp.div_const x
    have h' : HasDerivAt (fun u : ℝ => Real.exp (u * x) / x)
        (Real.exp (t * x) * x / x) t := by
      simpa only [id_eq, one_mul] using h
    apply h'.congr_deriv
    field_simp [hx]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 1)]
  norm_num only [one_mul, zero_mul, Real.exp_zero]
  field_simp [hx]

@[simp] lemma eta_zero : eta 0 = 1 := by
  simp [eta, intervalIntegral.integral_const]

lemma eta_continuous : Continuous eta := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [continuousAt_iff_punctured_nhds, eta_zero]
    have h := (Real.hasDerivAt_exp 0).tendsto_slope_zero
    have ht : Tendsto eta (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
      apply tendsto_congr' _ |>.mpr
        (show Tendsto (fun y : ℝ => y⁻¹ * (Real.exp y - 1)) (𝓝[≠] 0) (𝓝 1) by
          simpa only [zero_add, Real.exp_zero, inv_smul_eq_iff₀, smul_eq_mul] using h)
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [eta_eq_div hy]
      simp only [div_eq_mul_inv, mul_comm]
    exact ht
  · have hevent : eta =ᶠ[𝓝 x] (fun y : ℝ => (Real.exp y - 1) / y) := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      exact eta_eq_div hy
    exact ((Real.continuous_exp.sub continuous_const).continuousAt.div continuousAt_id hx).congr_of_eventuallyEq
      hevent

lemma eta_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt eta (eta x - (eta x - 1) / x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hevent : eta =ᶠ[𝓝 x] (fun y : ℝ => (Real.exp y - 1) / y) := by
    filter_upwards [eventually_ne_nhds hx0] with y hy
    exact eta_eq_div hy
  have hd := (Real.hasDerivAt_exp x).sub_const 1 |>.div (hasDerivAt_id x) hx0
  apply (hd.congr_of_eventuallyEq hevent).congr_deriv
  rw [eta_eq_div hx0]
  simp only [id_eq]
  field_simp [hx0]
  ring

lemma eta_slope_gt_half {x : ℝ} (hx : 0 < x) :
    (1 / 2 : ℝ) < eta x - (eta x - 1) / x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  let F : ℝ → ℝ := fun t => Real.exp (t * x) * (t * x - 1) / x ^ 2
  have hF : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt F (t * Real.exp (t * x)) t := by
    intro t _
    dsimp [F]
    have h := ((((hasDerivAt_id t).mul_const x).exp.mul
      (((hasDerivAt_id t).mul_const x).sub_const 1)).div_const (x ^ 2))
    have h' : HasDerivAt F
        ((Real.exp (t * x) * x * (t * x - 1) + Real.exp (t * x) * x) / x ^ 2) t := by
      simpa only [F, Pi.mul_apply, id_eq, one_mul] using h
    apply h'.congr_deriv
    field_simp [hx0]
    ring
  have hint : (∫ t in (0 : ℝ)..1, t * Real.exp (t * x)) =
      eta x - (eta x - 1) / x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((continuous_id.mul (Real.continuous_exp.comp
        (continuous_id.mul continuous_const))).intervalIntegrable 0 1)]
    rw [eta_eq_div hx0]
    dsimp [F]
    norm_num only [one_mul, zero_mul, Real.exp_zero]
    field_simp [hx0]
    ring
  rw [← hint]
  have hpos : 0 < ∫ t in (0 : ℝ)..1, t * (Real.exp (t * x) - 1) := by
    apply intervalIntegral.integral_pos (by norm_num)
    · fun_prop
    · intro t ht
      exact mul_nonneg ht.1.le
        (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg ht.1.le hx.le)))
    · refine ⟨1, by simp, ?_⟩
      simpa using Real.one_lt_exp_iff.mpr hx
  have hid : (∫ t in (0 : ℝ)..1, t) = (1 / 2 : ℝ) := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => t * t / 2) (f' := fun t : ℝ => t)
      (fun t _ => by
        have h := ((hasDerivAt_id t).mul (hasDerivAt_id t)).div_const 2
        simpa [Pi.mul_apply] using h)
      (continuous_id.intervalIntegrable 0 1)
    norm_num at hi ⊢
    exact hi
  rw [← hid]
  have hdecomp : (∫ t in (0 : ℝ)..1, t * Real.exp (t * x)) -
      (∫ t in (0 : ℝ)..1, t) =
      ∫ t in (0 : ℝ)..1, t * (Real.exp (t * x) - 1) := by
    have hi := intervalIntegral.integral_sub
      (f := fun t : ℝ => t * Real.exp (t * x)) (g := fun t : ℝ => t)
      ((continuous_id.mul (Real.continuous_exp.comp
        (continuous_id.mul continuous_const))).intervalIntegrable (μ := volume) 0 1)
      (continuous_id.intervalIntegrable (μ := volume) 0 1)
    rw [← hi]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  linarith

lemma eta_strictMonoOn : StrictMonoOn eta (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) eta_continuous.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  rw [(eta_hasDerivAt hx).deriv]
  linarith [eta_slope_gt_half hx]

lemma eta_tendsto_atTop : Tendsto eta atTop atTop := by
  have hquot := Real.tendsto_exp_div_pow_atTop 1
  have hbase : Tendsto (fun x : ℝ => Real.exp x / x ^ 1 - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) hquot)
  apply tendsto_atTop_mono' atTop ?_ hbase
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by linarith
  rw [eta_eq_div hx0]
  have hxinv : 1 / x ≤ 1 := by
    rw [div_le_one (by linarith : 0 < x)]
    exact hx
  simp only [pow_one]
  calc
    Real.exp x / x - 1 ≤ Real.exp x / x - 1 / x := sub_le_sub_left hxinv _
    _ = (Real.exp x - 1) / x := by ring

lemma eta_image_Ici : eta '' Ici (0 : ℝ) = Ici 1 := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    simpa using eta_strictMonoOn.monotoneOn (by simp : (0 : ℝ) ∈ Ici 0) hx hx
  · intro y hy
    obtain ⟨b, hb⟩ : ∃ b : ℝ, 0 ≤ b ∧ y ≤ eta b := by
      have he := (tendsto_atTop.1 eta_tendsto_atTop y).and (eventually_ge_atTop (0 : ℝ))
      rcases he.exists with ⟨b, hby, hb0⟩
      exact ⟨b, hb0, hby⟩
    rcases hb with ⟨hb0, hby⟩
    have hy' : y ∈ Icc (eta 0) (eta b) := by simpa using ⟨hy, hby⟩
    rcases intermediate_value_Icc hb0 eta_continuous.continuousOn hy' with ⟨x, hx, hxy⟩
    exact ⟨x, hx.1, hxy⟩

/-- Order isomorphism realizing the increasing inverse of `η : [0,∞) → [1,∞)`. -/
noncomputable def etaOrderIso : (Ici (0 : ℝ)) ≃o (Ici (1 : ℝ)) :=
  (eta_strictMonoOn.orderIso eta (Ici 0)).trans
    (OrderIso.setCongr (eta '' Ici (0 : ℝ)) (Ici 1) eta_image_Ici)

lemma etaOrderIso_apply (x : Ici (0 : ℝ)) : (etaOrderIso x : ℝ) = eta x := rfl

/-- Canonical global extension: the positive inverse on `(1,∞)`, and zero on `(-∞,1]`. -/
noncomputable def xi (s : ℝ) : ℝ :=
  ((etaOrderIso.symm ⟨max s 1, le_max_right s 1⟩ : Ici (0 : ℝ)) : ℝ)

lemma xi_continuous : Continuous xi := by
  exact continuous_subtype_val.comp
    (etaOrderIso.symm.continuous.comp
      ((continuous_id.max continuous_const).subtype_mk _))

lemma eta_xi (s : ℝ) : eta (xi s) = max s 1 := by
  change (etaOrderIso (etaOrderIso.symm ⟨max s 1, le_max_right s 1⟩) : ℝ) = _
  rw [etaOrderIso.apply_symm_apply]

lemma xi_pos {s : ℝ} (hs : 1 < s) : 0 < xi s := by
  have hmono := eta_strictMonoOn
  have hxi0 : 0 ≤ xi s := (etaOrderIso.symm ⟨max s 1, le_max_right s 1⟩).property
  refine lt_of_le_of_ne hxi0 ?_
  intro hzero
  have hxiz : xi s = 0 := hzero.symm
  have : eta (xi s) = 1 := by rw [hxiz, eta_zero]
  rw [eta_xi, max_eq_left hs.le] at this
  linarith

lemma xi_equation {s : ℝ} (hs : 1 < s) :
    Real.exp (xi s) - 1 = s * xi s := by
  have hxp := xi_pos hs
  have h := eta_xi s
  rw [max_eq_left hs.le, eta_eq_div (ne_of_gt hxp)] at h
  field_simp [ne_of_gt hxp] at h
  linarith

lemma xi_differentiableAt {s : ℝ} (hs : 1 < s) : DifferentiableAt ℝ xi s := by
  have hxp := xi_pos hs
  have hd := eta_hasDerivAt hxp
  apply (hd.of_local_left_inverse xi_continuous.continuousAt ?_ ?_).differentiableAt
  · linarith [eta_slope_gt_half hxp]
  · filter_upwards [Ioi_mem_nhds hs] with y hy
    rw [eta_xi, max_eq_left hy.le]

lemma xi_etaSlopeLower {s : ℝ} (hs : 1 < s) :
    (1 / 2 : ℝ) < s - (s - 1) / xi s := by
  have hxp := xi_pos hs
  have heta : eta (xi s) = s := by rw [eta_xi, max_eq_left hs.le]
  have h := eta_slope_gt_half hxp
  rw [heta] at h
  exact h

/-- The canonical inverse closes the exact weak Proposition 10.20 interface. -/
theorem canonicalXi_proposition1020 : Section10Lemma1028.Proposition1020Xi xi where
  continuous := xi_continuous
  positive := fun s hs => @xi_pos s hs
  equation := fun s hs => @xi_equation s hs
  differentiableAt := fun s hs => @xi_differentiableAt s hs
  etaSlopeLower := fun s hs => @xi_etaSlopeLower s hs

end Section10CanonicalXi
