import MathlibNt.SieveTheory.LiLiuFouvryG9BaseEuler
import MathlibNt.SieveTheory.LiLiuFouvryG9WFLevel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter Finset
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The real initial branch, with the sqrt logarithm cancelled exactly. -/
theorem fouvryG9MainScalar_initial {N : ℕ} {Q : ℝ}
    (hN : 1 < (N : ℝ)) (hQ : 1 < Q) (hQN : Q ≤ N) :
    jr1965F (Real.log Q / Real.log (Real.sqrt N)) =
      Real.exp Real.eulerMascheroniConstant * Real.log N / Real.log Q ∧
    Real.exp Real.eulerMascheroniConstant ≤
      jr1965F (Real.log Q / Real.log (Real.sqrt N)) := by
  have hn := Real.log_pos hN
  have hq := Real.log_pos hQ
  have hz : Real.log (Real.sqrt N) = Real.log N / 2 :=
    Real.log_sqrt (Nat.cast_nonneg N)
  have hqn := Real.log_le_log (by linarith : 0 < Q) hQN
  have hs : Real.log Q / Real.log (Real.sqrt N) ≤ 3 := by
    rw [hz]
    apply (div_le_iff₀ (by positivity : 0 < Real.log (N : ℝ) / 2)).2
    linarith
  rw [jr1965F_eq_of_le_three hs, hz]
  constructor
  · field_simp
  · apply (le_div_iff₀ (div_pos hq (by positivity))).2
    have hr : Real.log Q / (Real.log (N : ℝ) / 2) ≤ 2 :=
      (div_le_iff₀ (by positivity)).2 (by linarith)
    nlinarith [Real.exp_pos Real.eulerMascheroniConstant]

/-- Load-bearing normalization of the actual base product and actual upper factor.
The hypotheses here are precisely the three near-one estimates, discharged below. -/
theorem fouvryG9MainScalar_normalize {N : ℕ} {Q C K η ζ A : ℝ}
    (hN : 1 < (N : ℝ)) (hQ : 1 < Q) (hQN : Q ≤ N) (hζ : 0 < ζ)
    (hV : 0 ≤ fouvryG9BaseEuler N (Real.sqrt N))
    (hbase : fouvryG9BaseEuler N (Real.sqrt N) * Real.log N ≤
      4 * Real.exp (-Real.eulerMascheroniConstant) * (1+ζ) *
        SingularSeries.liuSingularSeries N)
    (hA : 0 ≤ A) (hAu : A ≤ 1+ζ)
    (herr : C*(η+(η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ))) ≤
      ζ*Real.exp Real.eulerMascheroniConstant) :
    fouvryG9BaseEuler N (Real.sqrt N)*A*fouvryG9UpperFactor N Q C K η ≤
      4*(1+ζ)^3*SingularSeries.liuSingularSeries N/Real.log Q := by
  obtain ⟨hF,hFlo⟩ := fouvryG9MainScalar_initial hN hQ hQN
  have hF0 : 0 ≤ jr1965F (Real.log Q / Real.log (Real.sqrt N)) :=
    (Real.exp_pos _).le.trans hFlo
  have hu : fouvryG9UpperFactor N Q C K η ≤
      (1+ζ)*jr1965F (Real.log Q / Real.log (Real.sqrt N)) := by
    unfold fouvryG9UpperFactor
    nlinarith [mul_le_mul_of_nonneg_left hFlo hζ.le]
  have hn := Real.log_pos hN
  have hq := Real.log_pos hQ
  have he : Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp Real.eulerMascheroniConstant = 1 := by
    rw [← Real.exp_add]; simp
  calc
    _ ≤ fouvryG9BaseEuler N (Real.sqrt N)*A*
        ((1+ζ)*jr1965F (Real.log Q / Real.log (Real.sqrt N))) :=
      mul_le_mul_of_nonneg_left hu (mul_nonneg hV hA)
    _ ≤ fouvryG9BaseEuler N (Real.sqrt N)*(1+ζ)*
        ((1+ζ)*jr1965F (Real.log Q / Real.log (Real.sqrt N))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAu hV)
        (mul_nonneg (by linarith) hF0)
    _ = (fouvryG9BaseEuler N (Real.sqrt N)*Real.log N)*
        ((1+ζ)^2*Real.exp Real.eulerMascheroniConstant/Real.log Q) := by rw [hF]; ring
    _ ≤ (4*Real.exp (-Real.eulerMascheroniConstant)*(1+ζ)*
        SingularSeries.liuSingularSeries N)*
        ((1+ζ)^2*Real.exp Real.eulerMascheroniConstant/Real.log Q) :=
      mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = 4*(1+ζ)^3*SingularSeries.liuSingularSeries N*
        (Real.exp (-Real.eulerMascheroniConstant)*Real.exp Real.eulerMascheroniConstant)/Real.log Q := by ring
    _ = _ := by rw [he]; ring

/-- Elementary budget: the entire correction cube pays only one near-one factor. -/
theorem fouvryG9MainScalar_cube {x : ℝ} (hx : 0 ≤ x) (hxu : x ≤ 1) :
    (1+x)^3 ≤ 1+7*x := by
  have h2 : x^2 ≤ x := by nlinarith
  have h3 : x^3 ≤ x^2 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr h2)]
  nlinarith

/-- The complete scalar payment. Eta is fixed before delta, N and the short scale.
No scalar estimate is assumed: the product normalization and all tails are paid. -/
theorem fouvryG9MainScalar_payment (C K τ : ℝ) (hC : 0 < C) (_hK : 1 < K)
    (hτ : 0 < τ) :
    ∃ η : ℝ, 0 < η ∧ η < 1/8 ∧ ∀ δ : ℝ, 0 ≤ δ → δ < 1/4 →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
        ∀ T : ℝ, 1 ≤ T → T ≤ (N : ℝ)^(1/10 : ℝ) →
          let Q := (N : ℝ)^(5/9-δ)/T^(5/9 : ℝ)
          fouvryG9BaseEuler N (Real.sqrt N)*
            (1+1/((N : ℝ)^(4/53 : ℝ)/2-2))^3*fouvryG9UpperFactor N Q C K η ≤
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
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).eventually_ge_atTop
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
  have hd : 0 < (N : ℝ)^(4/53 : ℝ)/2-2 := by
    have : 0 < 7/ζ := by positivity
    linarith
  have hx : 0 ≤ 1/((N : ℝ)^(4/53 : ℝ)/2-2) := by positivity
  have hxu : 1/((N : ℝ)^(4/53 : ℝ)/2-2) ≤ ζ/7 := by
    apply (div_le_iff₀ hd).2
    have hg' : 7/ζ ≤ (N : ℝ)^(4/53 : ℝ)/2-2 := by linarith
    have hh := mul_le_mul_of_nonneg_left hg' (show 0 ≤ ζ/7 by positivity)
    field_simp at hh
    nlinarith
  have hcorr : (1+1/((N : ℝ)^(4/53 : ℝ)/2-2))^3 ≤ 1+ζ := by
    have hx1 : 1/((N : ℝ)^(4/53 : ℝ)/2-2) ≤ 1 := hxu.trans (by linarith)
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
    (by positivity : 0 ≤ (1+1/((N : ℝ)^(4/53 : ℝ)/2-2))^3) hcorr herr
  exact hnorm.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 4*(1+ζ)^3 ≤ 4*(1+τ)) hSS)
      (Real.log_pos hQ1).le)

#print axioms fouvryG9MainScalar_initial
#print axioms fouvryG9MainScalar_normalize
#print axioms fouvryG9MainScalar_payment
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
