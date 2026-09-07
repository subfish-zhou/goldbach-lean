import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorSieveFactor

open Filter
open scoped Topology
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The finite 21-factor rough correction tends to one. The threshold is
independent of every changing rectangle and prime. -/
theorem goldbachG11EulerCorrection_eventually (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → goldbachG11EulerCorrection N ≤ 1+ζ := by
  have hd : Tendsto (fun x : ℝ => x^(4/53 : ℝ)-2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).eventually
      (eventually_ge_atTop (b+2))] with x hx
    linarith
  have hi := tendsto_inv_atTop_zero.comp hd
  have ht : Tendsto (fun x : ℝ => (1+1/(x^(4/53 : ℝ)-2))^21) atTop (𝓝 1) := by
    simpa only [one_div,add_zero,one_pow,Function.comp_apply] using (hi.const_add 1).pow 21
  obtain ⟨M,hM⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (show (1 : ℝ) < 1+ζ by linarith)))
  refine ⟨max 4 ⌈M⌉₊,le_max_left _ _,?_⟩
  intro N hN
  exact (hM N ((Nat.le_ceil M).trans (by exact_mod_cast (le_max_right _ _).trans hN))).le

/-- Pay the genuine decaying external-family defect uniformly from the
quarter-log lower envelope, before any changing level is supplied. -/
theorem goldbachG11FamilyError_uniform (C K θ η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ,
    (1/4 : ℝ)*Real.log (N : ℝ) ≤ Real.log Q →
      4*Real.exp (-Real.eulerMascheroniConstant)*goldbachG11FamilyErrorFactor Q C K θ ≤
        4*Real.exp (-Real.eulerMascheroniConstant)*C*θ+η := by
  let D := 4*Real.exp (-Real.eulerMascheroniConstant)*C*(θ^8)⁻¹*Real.exp (6*K+2)
  have ht : Tendsto (fun y : ℝ => D*y^(-(1/3 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/3)).const_mul D
  obtain ⟨M,hM⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hη))
  refine ⟨max 4 ⌈Real.exp (4*max M 1)⌉₊,le_max_left _ _,?_⟩
  intro N hN Q hQ
  have hn4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he : Real.exp (4*max M 1) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  have hl := (Real.le_log_iff_exp_le hn).2 he
  have hMQ : M ≤ Real.log Q := by have hh := le_max_left M (1 : ℝ); linarith
  have hb := (hM (Real.log Q) hMQ).le
  calc
    _ = 4*Real.exp (-Real.eulerMascheroniConstant)*C*θ+D*Real.log Q^(-(1/3 : ℝ)) := by
      unfold goldbachG11FamilyErrorFactor D
      ring
    _ ≤ _ := add_le_add (le_refl _) hb

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig