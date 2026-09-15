import Wu08FourMainDensity

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace Wu08FirstPrimeFour.Normalization

/-- The logarithmic coordinate of the genuine buffered short scale. -/
def cellCoord (N : ℕ) (ρ : ℝ) (k : Key) : ℝ := log ((2/3 : ℝ)*ρ^k.1)/log N
/-- Wu's improved small-first-prime weight, not the uniform weight 8. -/
def cellWeight (N : ℕ) (ρ : ℝ) (k : Key) : ℝ := (36/5)/(1-cellCoord N ρ k)
def familyDefect (Q C K η : ℝ) : ℝ :=
  C*(η+(η^8)⁻¹*exp (6*K+2)*log Q^(-(1/3 : ℝ)))

theorem level_log_geometry {N : ℕ} {ρ δ : ℝ} (hN : (4 : ℝ) ≤ N)
    {k : Key} (hT : 1 ≤ (2/3 : ℝ)*ρ^k.1)
    (hTu : (2/3 : ℝ)*ρ^k.1 ≤ (N : ℝ)^(1/10 : ℝ)) :
    0 ≤ cellCoord N ρ k ∧ cellCoord N ρ k ≤ 1/10 ∧
      log (level N ρ δ k) = ((5/9)*(1-cellCoord N ρ k)-δ)*log N := by
  have hn : (0 : ℝ) < N := by linarith
  have hln : 0 < log (N : ℝ) := log_pos (by linarith)
  have ht : 0 < (2/3 : ℝ)*ρ^k.1 := by linarith
  have hlo : 0 ≤ log ((2/3 : ℝ)*ρ^k.1) := log_nonneg hT
  have hhi := log_le_log ht hTu
  rw [log_rpow hn] at hhi
  refine ⟨div_nonneg hlo hln.le,(div_le_iff₀ hln).mpr (by linarith),?_⟩
  unfold level cellCoord
  rw [log_div (rpow_pos_of_pos hn _).ne' (rpow_pos_of_pos ht _).ne',log_rpow hn,log_rpow ht]
  field_simp
  ring

theorem cellWeight_bounds {N : ℕ} {ρ : ℝ} {k : Key}
    (_hx : 0 ≤ cellCoord N ρ k) (hxu : cellCoord N ρ k ≤ 1/10) :
    0 ≤ cellWeight N ρ k ∧ cellWeight N ρ k ≤ 8 := by
  have hp : 0 < 1-cellCoord N ρ k := by linarith
  constructor
  · exact div_nonneg (by norm_num) hp.le
  · unfold cellWeight
    apply (div_le_iff₀ hp).mpr
    linarith

theorem level_weight_loss {N : ℕ} {ρ δ : ℝ} (hN : (4 : ℝ) ≤ N)
    (hδ : 0 ≤ δ) (hδu : δ < 1/4) {k : Key}
    (hT : 1 ≤ (2/3 : ℝ)*ρ^k.1)
    (hTu : (2/3 : ℝ)*ρ^k.1 ≤ (N : ℝ)^(1/10 : ℝ)) :
    (1/4 : ℝ)*log N ≤ log (level N ρ δ k) ∧
      4*log N/log (level N ρ δ k) ≤ cellWeight N ρ k+32*δ := by
  obtain ⟨_,hxu,he⟩ := level_log_geometry (δ := δ) hN hT hTu
  have hln : 0 < log (N : ℝ) := log_pos (by linarith)
  let b : ℝ := (5/9)*(1-cellCoord N ρ k)
  have hb : 1/2 ≤ b := by dsimp [b]; linarith
  have hb0 : 0 < b := by linarith
  have hbd : 0 < b-δ := by linarith
  have hh : (1/8 : ℝ) ≤ b*(b-δ) := by
    have hm := mul_le_mul hb (show (1/4 : ℝ) ≤ b-δ by linarith) (by norm_num) hb0.le
    norm_num at hm
    exact hm
  constructor
  · rw [he]
    exact mul_le_mul_of_nonneg_right (by dsimp [b] at hb; linarith) hln.le
  · calc
      _ = 4/(b-δ) := by rw [he]; change 4*log (N : ℝ)/((b-δ)*log N)=_; field_simp
      _ = 4/b+4*δ/(b*(b-δ)) := by field_simp; ring
      _ ≤ 4/b+4*δ/(1/8 : ℝ) := add_le_add (le_refl _)
        (div_le_div_of_nonneg_left (by positivity : 0 ≤ 4*δ) (by norm_num) hh)
      _ = cellWeight N ρ k+32*δ := by unfold cellWeight b; field_simp; ring

/-- Exact Euler-Mascheroni cancellation at the actual level; no m-only density
substitution occurs. This coefficient multiplies full-cofactor cellMass. -/
theorem upperFactor_scaled {N : ℕ} {Q C K η : ℝ} (hN : (4 : ℝ) ≤ N)
    (hQ : 0 < Q) (hlQ : 0 < log Q) (hQN : Q ≤ N) :
    4*exp (-eulerMascheroniConstant)*fouvryG9UpperFactor N Q C K η =
      4*log N/log Q+4*exp (-eulerMascheroniConstant)*familyDefect Q C K η := by
  have hn : (0 : ℝ) < N := by linarith
  have hln : 0 < log (N : ℝ) := log_pos (by linarith)
  have hc : log Q/log (sqrt N) ≤ 3 := by
    rw [log_sqrt hn.le]
    apply (div_le_iff₀ (by positivity : 0 < log (N : ℝ)/2)).mpr
    have hh := log_le_log hQ hQN
    linarith
  unfold fouvryG9UpperFactor familyDefect
  rw [jr1965F_eq_of_le_three hc,log_sqrt hn.le,exp_neg]
  field_simp

/-- Fixed eta's decaying defect is controlled before all changing levels.
Only C*eta remains, explicitly paid by choosing eta after the target tolerance. -/
theorem familyDefect_eventually (C K η : ℝ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ Q : ℝ,
      (1/4 : ℝ)*log N ≤ log Q →
      4*exp (-eulerMascheroniConstant)*familyDefect Q C K η ≤
        4*exp (-eulerMascheroniConstant)*C*η+ζ := by
  let D := 4*exp (-eulerMascheroniConstant)*C*(η^8)⁻¹*exp (6*K+2)
  have ht : Tendsto (fun y : ℝ => D*y^(-(1/3 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/3)).const_mul D
  obtain ⟨M,hM⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hζ))
  refine ⟨max 4 (exp (4*max M 1)),?_⟩
  intro N hN Q hQ
  have hn : (0 : ℝ) < N := by have := (le_max_left _ _).trans hN; linarith
  have he := (le_max_right _ _).trans hN
  have hl := (le_log_iff_exp_le hn).mpr he
  have hMQ : M ≤ log Q := by have := le_max_left M (1 : ℝ); linarith
  have hbound := (hM (log Q) hMQ).le
  calc
    _ = 4*exp (-eulerMascheroniConstant)*C*η+D*log Q^(-(1/3 : ℝ)) := by
      unfold familyDefect D
      ring
    _ ≤ _ := add_le_add (le_refl _) hbound

#print axioms level_weight_loss
#print axioms upperFactor_scaled
#print axioms familyDefect_eventually
end Wu08FirstPrimeFour.Normalization
