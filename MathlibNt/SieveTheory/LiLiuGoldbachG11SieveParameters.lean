import MathlibNt.SieveTheory.LiLiuGoldbachB8NormalizedMainMass
import MathlibNt.SieveTheory.LiLiuGoldbachWeightG11BuchstabConsumed

open Filter
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

def goldbachG11SieveLevel (B : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)^((1 : ℝ)/2)/Real.log (N : ℝ)^(B+1)
def goldbachG11SieveCutoff (B : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (goldbachG11SieveLevel B N)

/-- Reuse the existing public B8 cutoff theorem; only the actual G11 level cap is added. -/
theorem goldbachG11SieveParameters_eventually (B K τ : ℝ)
    (hB : 0 ≤ B) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀,
      let Δ := goldbachG11SieveLevel B N
      let Z := goldbachG11SieveCutoff B N
      max 2 K ≤ Z ∧ Z ≤ (N : ℝ)^((1 : ℝ)/4) ∧ 0 < Δ ∧
      2 = Real.log Δ/Real.log Z ∧ Δ ≤ Real.sqrt N/Real.log (N : ℝ)^B ∧
      0 < Real.log Z ∧ Real.log (N : ℝ)/Real.log Z ≤ 4*(1+τ) := by
  obtain ⟨G,hG,hgeom⟩ := goldbachB8Plus_normalized_cutoff_geometry B K τ hB hτ hτ1
  have hlogs : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  obtain ⟨L,hL⟩ := eventually_atTop.mp hlogs
  refine ⟨max G L,hG.trans (le_max_left _ _),?_⟩
  intro N hN
  have hG' : G ≤ N := (le_max_left _ _).trans hN
  have hlog1 := hL N ((le_max_right _ _).trans hN)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N from lt_of_lt_of_le (by omega) (hG.trans hG'))
  have hlog0 : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  obtain ⟨hZ,hZq,_,_,hs,hlogZ,hratio⟩ := hgeom N hG'
  refine ⟨hZ,hZq,?_,hs.symm,?_,hlogZ,hratio⟩
  · exact div_pos (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos hlog0 _)
  · change (N : ℝ)^((1 : ℝ)/2)/Real.log (N : ℝ)^(B+1) ≤ _
    rw [Real.sqrt_eq_rpow]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _)
      (Real.rpow_pos_of_pos hlog0 _) (Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith))

/-- All sieve parameters are now concrete functions of N. The remaining main term
is the actual finite Buchstab sum, not the paper's tighter low-band constant. -/
theorem goldbachWeightG11_le_concreteBuchstabSieve (A ρ δ η : ℝ)
    (hA : 0 < A) (hρ : 0 < ρ) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε : ℝ), 0 ≤ ε →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
      goldbachG11BuchstabSieveEnvelope N (goldbachG11SieveCutoff B N) A C ρ η +
        δ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨B,C,z₀,hB,hC,K,hK,hpaid⟩ := goldbachWeightG11_le_buchstabSieve A ρ δ η hA hρ hδ hη
  obtain ⟨L,_,hgeom⟩ := goldbachG11SieveParameters_eventually B z₀ 1 hB.le (by norm_num) le_rfl
  refine ⟨B,C,hB,hC,max K L,hK.trans (le_max_left _ _),?_⟩
  intro N hN hEven ε hε
  obtain ⟨hZ,_,hΔ,hs,hlevel,_,_⟩ := hgeom N ((le_max_right _ _).trans hN)
  exact hpaid N ((le_max_left _ _).trans hN) hEven ε hε
    (goldbachG11SieveCutoff B N) (goldbachG11SieveLevel B N)
    ((le_max_right _ _).trans hZ) ((le_max_left _ _).trans hZ) hΔ hs hlevel

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig