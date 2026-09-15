import OriginalScalar

noncomputable section
open Finset Filter
open MathlibNt.SieveTheory
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace OriginalU8

/-- A local normalized center, not the paper F8 integral or a full-mass theorem.
Eta is actually selected before delta and the common cutoff. -/
theorem actualCenter_normalized (τ : ℝ) (hτ : 0 < τ) :
    ∃ η : ℝ, 0 < η ∧ η < 1/8 ∧ ∀ δ : ℝ, 0 ≤ δ → δ < 1/4 →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      ∀ e ρ : ℝ, 0 < e → 1 < ρ → ρ ≤ 5/4 → ∀ k : ℕ × ℕ × ℕ,
      Occupied N e ρ k →
      actualCenter N ρ δ η k (fouvryG9SievePrimes N (Real.sqrt N)) (Real.sqrt N) ≤
        4*(1+τ)*SingularSeries.liuSingularSeries N / Real.log (level N ρ δ k) *
          rectangleMass N ρ k := by
  obtain ⟨C,hC,K,hK,hmain⟩ := actualCenter_upper
  obtain ⟨η,hη,hηu,hpay⟩ := scalar_payment (100/1327) C K τ (by norm_num) hC hK hτ
  refine ⟨η,hη,hηu,?_⟩
  intro δ hδ hδu
  obtain ⟨Nd,hd⟩ := hmain δ η hδ hδu hη hηu
  obtain ⟨Ns,hs⟩ := hpay δ hδ hδu
  obtain ⟨Ng,hg⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 6 0 (100/1327) (by norm_num))
  refine ⟨max Nd (max Ns Ng),?_⟩
  intro N hN hEven e ρ he hρ hρu k hne
  have hNd := (le_max_left _ _).trans hN
  have hr := (le_max_right _ _).trans hN
  have hNs := (le_max_left _ _).trans hr
  have hNg := (le_max_right _ _).trans hr
  have h6 : 6 ≤ (N : ℝ)^(100/1327 : ℝ) := by simpa using hg N hNg
  obtain ⟨_,_,_,hlo,hhi⟩ := geometry he hρ hρu hne
  have hT : 1 ≤ (2/3 : ℝ)*ρ^k.1 := by linarith
  have hm := (hd N hNd hEven e ρ he hρ hρu k hne).2.2
  have hp := hs N hNs hEven ((2/3 : ℝ)*ρ^k.1) hT hhi
  calc
    _ ≤ _ := hm
    _ = (fouvryG9BaseEuler N (Real.sqrt N)*
        (1+1/((N : ℝ)^(100/1327 : ℝ)/2-2))^3 *
        fouvryG9UpperFactor N (level N ρ δ k) C K η) * rectangleMass N ρ k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (rectangleMass_nonneg N ρ k)

/-- Exact original global-level logarithm. x is the true log short-scale,
not a new optimization cutoff or an altered prime window. -/
theorem global_level_log {N T : ℝ} (hN : 1 < N) (hT : 0 < T) (δ : ℝ) :
    Real.log (N^(5/9-δ)/T^(5/9 : ℝ)) =
      Real.log N * ((5/9 : ℝ)*(1-Real.log T/Real.log N)-δ) := by
  rw [Real.log_div (Real.rpow_pos_of_pos (by linarith) _).ne'
    (Real.rpow_pos_of_pos hT _).ne', Real.log_rpow (by linarith : 0 < N),
    Real.log_rpow hT]
  field_simp [ne_of_gt (Real.log_pos hN)]
  ring

/-- The internal-level factor is retained exactly rather than dropped at fixed eta. -/
theorem internal_level_log {N T : ℝ} (hN : 1 < N) (hT : 0 < T) (δ η : ℝ) :
    Real.log (externalInternalLevel (N^(5/9-δ)/T^(5/9 : ℝ)) η) =
      (1+η+η^9)⁻¹ * (Real.log N * ((5/9 : ℝ)*(1-Real.log T/Real.log N)-δ)) := by
  unfold externalInternalLevel
  rw [Real.log_rpow (div_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos hT _)), global_level_log hN hT]

/-- Exact normalization along T=N^x, with the original 5/9 level. -/
theorem global_normalization {N : ℝ} (hN : 1 < N) (x δ : ℝ) :
    Real.log N / (2*Real.log (N^(5/9-δ)/(N^x)^(5/9 : ℝ))) =
      1/(2*((5/9 : ℝ)*(1-x)-δ)) := by
  rw [global_level_log hN (Real.rpow_pos_of_pos (by linarith) _),
    Real.log_rpow (by linarith : 0 < N)]
  have hn : Real.log N ≠ 0 := ne_of_gt (Real.log_pos hN)
  field_simp

/-- At fixed parameters the internal normalization costs 1+eta+eta^9. -/
theorem internal_normalization {N : ℝ} (hN : 1 < N) (x δ η : ℝ) :
    Real.log N /
      (2*Real.log (externalInternalLevel (N^(5/9-δ)/(N^x)^(5/9 : ℝ)) η)) =
      (1+η+η^9)/(2*((5/9 : ℝ)*(1-x)-δ)) := by
  rw [internal_level_log hN (Real.rpow_pos_of_pos (by linarith) _) δ η,
    Real.log_rpow (by linarith : 0 < N)]
  have hn : Real.log N ≠ 0 := ne_of_gt (Real.log_pos hN)
  simp only [mul_div_cancel_right₀ _ hn]
  rw [div_mul_eq_div_div, div_mul_eq_div_div]
  field_simp

/-- After N tends to infinity at fixed parameters, the two-parameter small
eta/delta path recovers the original 9/[10(1-x)] local level normalization. -/
theorem normalization_limit (x : ℝ) (hx : x < 1) :
    Tendsto (fun t : ℝ => (1+t+t^9)/(2*((5/9 : ℝ)*(1-x)-t))) (nhds 0)
      (nhds (9/(10*(1-x)))) := by
  have hd : (2 : ℝ)*((5/9)*(1-x)-0) ≠ 0 := by nlinarith
  have h : Tendsto (fun t : ℝ => (1+t+t^9)/(2*((5/9 : ℝ)*(1-x)-t))) (nhds 0)
      (nhds ((1+(0 : ℝ)+0^9)/(2*((5/9 : ℝ)*(1-x)-0)))) :=
    ((tendsto_const_nhds.add tendsto_id).add (tendsto_id.pow 9)).div
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub tendsto_id)) hd
  have he : (9/(10*(1-x))) = ((1+(0 : ℝ)+0^9)/(2*((5/9 : ℝ)*(1-x)-0))) := by
    norm_num
    field_simp
    norm_num
  rw [he]
  exact h

#print axioms actualCenter_normalized
#print axioms global_level_log
#print axioms internal_normalization
#print axioms normalization_limit
end OriginalU8
