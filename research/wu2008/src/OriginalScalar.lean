import OriginalDensity

noncomputable section
open Filter Finset
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace OriginalU8

/-- Alpha-independent scalar payment, using the proved Mertens and WF cores.
The exponent is arbitrary positive, not the Li--Liu terminal window. -/
theorem scalar_payment (a C K τ : ℝ) (ha : 0 < a) (hC : 0 < C) (_hK : 1 < K)
    (hτ : 0 < τ) :
    ∃ η : ℝ, 0 < η ∧ η < 1/8 ∧ ∀ δ : ℝ, 0 ≤ δ → δ < 1/4 →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
        ∀ T : ℝ, 1 ≤ T → T ≤ (N : ℝ)^(1/10 : ℝ) →
          let Q := (N : ℝ)^(5/9-δ)/T^(5/9 : ℝ)
          fouvryG9BaseEuler N (Real.sqrt N)*
            (1+1/((N : ℝ)^a/2-2))^3*fouvryG9UpperFactor N Q C K η ≤
              4*(1+τ)*SingularSeries.liuSingularSeries N/Real.log Q := by
  let ζ : ℝ := min (τ/7) 1
  have hζ : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζ1 : ζ ≤ 1 := min_le_right _ _
  have hζτ : 7*ζ ≤ τ := by have := min_le_left (τ/7) (1 : ℝ); dsimp [ζ]; linarith
  have hbudget : (1+ζ)^3 ≤ 1+τ :=
    (fouvryG9MainScalar_cube hζ.le hζ1).trans (by linarith)
  let η : ℝ := min (1/16) (ζ*Real.exp Real.eulerMascheroniConstant/(4*C))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηu : η < 1/8 := (min_le_left _ _).trans_lt (by norm_num)
  have hηpay : C*η ≤ ζ*Real.exp Real.eulerMascheroniConstant/2 := by
    have h := (le_div_iff₀ (show 0 < 4*C by positivity)).1 (min_le_right (1/16) (ζ*Real.exp Real.eulerMascheroniConstant/(4*C)))
    change η*(4*C) ≤ ζ*Real.exp Real.eulerMascheroniConstant at h
    nlinarith [Real.exp_pos Real.eulerMascheroniConstant]
  have htail : Tendsto (fun Q : ℝ =>
      C*((η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ)))) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/3)).comp
      Real.tendsto_log_atTop
    simpa only [mul_zero, Function.comp_apply] using (h.const_mul ((η^8)⁻¹*Real.exp (6*K+2))).const_mul C
  obtain ⟨Q₀,hQ₀⟩ := eventually_atTop.mp
    ((tendsto_order.1 htail).2 (ζ*Real.exp Real.eulerMascheroniConstant/2) (by positivity))
  obtain ⟨Nb,hb⟩ := fouvryG9BaseEuler_sqrt_upper ζ hζ
  obtain ⟨Nc,hc⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop ha).eventually_ge_atTop
      (2*(2+7/ζ)))
  refine ⟨η,hη,hηu,?_⟩
  intro δ hδ hδu
  obtain ⟨Nw,hw⟩ := g9WF_exists_internal_level_gate hδ (by linarith) hη (max Q₀ 4)
  refine ⟨max 4 (max Nb (max Nc Nw)),?_⟩
  intro N hN hEven T hT hTu
  have hN4 : (4 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hrest := (le_max_right _ _).trans hN
  have hNb := (le_max_left _ _).trans hrest
  have hrest2 := (le_max_right _ _).trans hrest
  have hNc := (le_max_left _ _).trans hrest2
  have hNw := (le_max_right _ _).trans hrest2
  have hN1 : 1 < (N : ℝ) := by linarith
  let Q := (N : ℝ)^(5/9-δ)/T^(5/9 : ℝ)
  obtain ⟨_,_,hQQ,_,hQN⟩ := hw N T hNw hT hTu
  have hQ4 : 4 ≤ Q := (le_max_right _ _).trans hQQ
  have hQ1 : 1 < Q := by linarith
  have herr : C*(η+(η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ))) ≤
      ζ*Real.exp Real.eulerMascheroniConstant := by
    have ht := hQ₀ Q ((le_max_left _ _).trans hQQ)
    linarith
  have hg := hc (N : ℝ) hNc
  have hd : 0 < (N : ℝ)^a/2-2 := by
    have : 0 < 7/ζ := by positivity
    linarith
  have hx : 0 ≤ 1/((N : ℝ)^a/2-2) := by positivity
  have hxu : 1/((N : ℝ)^a/2-2) ≤ ζ/7 := by
    apply (div_le_iff₀ hd).2
    have hg' : 7/ζ ≤ (N : ℝ)^a/2-2 := by linarith
    have hh := mul_le_mul_of_nonneg_left hg' (show 0 ≤ ζ/7 by positivity)
    field_simp at hh
    nlinarith
  have hcorr : (1+1/((N : ℝ)^a/2-2))^3 ≤ 1+ζ := by
    have hx1 : 1/((N : ℝ)^a/2-2) ≤ 1 := hxu.trans (by linarith)
    have hh := fouvryG9MainScalar_cube hx hx1
    linarith
  have hV : 0 ≤ fouvryG9BaseEuler N (Real.sqrt N) := by
    unfold fouvryG9BaseEuler
    apply prod_nonneg
    intro p hp
    have hodd := (fouvryG9SievePrimes_odd hEven (Real.sqrt N) p hp).2
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hodd
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by linarith : 0 < (p : ℝ)-1)).2
    linarith
  have hbase := hb N hNb hEven
  have hSS : 0 ≤ SingularSeries.liuSingularSeries N := by
    have hh := (mul_nonneg hV (Real.log_pos hN1).le).trans hbase
    exact nonneg_of_mul_nonneg_right hh (by positivity)
  have hnorm := fouvryG9MainScalar_normalize hN1 hQ1 hQN hζ hV hbase
    (by positivity : 0 ≤ (1+1/((N : ℝ)^a/2-2))^3) hcorr herr
  exact hnorm.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 4*(1+ζ)^3 ≤ 4*(1+τ)) hSS)
      (Real.log_pos hQ1).le)

#print axioms scalar_payment
end OriginalU8
