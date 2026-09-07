import MathlibNt.SieveTheory.LiLiuGoldbachG11GridSubpowerBudget

open Filter
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuPrereqWF
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11OrdinaryLevel (N : ℕ) (δ : ℝ) : ℝ := (N : ℝ)^(1/2-δ)

/-- A fixed positive power saving pays the ordinary logarithmic level loss
at analysis size 4N, while the level itself is still measured against original N. -/
theorem goldbachG11OrdinaryLevel_in_source (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG11OrdinaryLevel N δ ≤ Real.sqrt (4*(N : ℝ))/Real.log (4*(N : ℝ))^B := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (TransportAbsorption.eventually_log_power_budget ((4 : ℝ)^δ) B hδ)
  refine ⟨max 4 ⌈M⌉₊,le_max_left _ _,?_⟩
  intro N hN
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast (le_max_left _ _).trans hN
  have hn : (0 : ℝ) < N := by linarith
  have hNM : M ≤ (N : ℝ) := (Nat.le_ceil M).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  have hb := hM (4*(N : ℝ)) (by linarith)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hn.le] at hb
  have hlogpow : Real.log (4*(N : ℝ))^B ≤ (N : ℝ)^δ :=
    (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) δ)).mp hb
  have hlog : 0 < Real.log (4*(N : ℝ)) := Real.log_pos (by nlinarith)
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog B)).2
  calc
    _ ≤ goldbachG11OrdinaryLevel N δ*(N : ℝ)^δ :=
      mul_le_mul_of_nonneg_left hlogpow (Real.rpow_nonneg hn.le _)
    _ = (N : ℝ)^(1/2 : ℝ) := by
      unfold goldbachG11OrdinaryLevel
      rw [← Real.rpow_add hn]
      congr 1
      ring
    _ ≤ _ := by rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt (by linarith)

theorem goldbachG11OrdinaryLevel_eq_low_at_boundary {N : ℕ} (hn : 0 < (N : ℝ)) (δ : ℝ) :
    (N : ℝ)^(5/9-δ)/((N : ℝ)^(1/10 : ℝ))^(5/9 : ℝ) = goldbachG11OrdinaryLevel N δ := by
  unfold goldbachG11OrdinaryLevel
  rw [← Real.rpow_mul hn.le,← Real.rpow_sub hn]
  congr 1
  ring

/-- No level-size or large-cutoff gates are supplied by the eventual caller. -/
theorem goldbachG11OrdinaryLevel_gates {δ θ : ℝ}
    (hδ : 0 ≤ δ) (hδu : δ < 1/2) (hθ : 0 < θ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      4 ≤ (N : ℝ)^(4/53 : ℝ) ∧ 1 ≤ goldbachG11OrdinaryLevel N δ ∧
      2 ≤ externalInternalLevel (goldbachG11OrdinaryLevel N δ) θ ∧
      goldbachG11OrdinaryLevel N δ ≤ N := by
  obtain ⟨M,hM⟩ := g9WF_exists_internal_level_gate hδ hδu hθ 1
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max 4 ⌈max M B⌉₊,le_max_left _ _,?_⟩
  intro N hN
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast (le_max_left _ _).trans hN
  have hn1 : (1 : ℝ) ≤ N := by linarith
  have hn : (0 : ℝ) < N := by linarith
  have hbase : max M B ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  obtain ⟨hNM,hNB⟩ := max_le_iff.mp hbase
  have hT : (1 : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  obtain ⟨_hn,hQ,_hQ0,hD,hQN⟩ := hM N ((N : ℝ)^(1/10 : ℝ)) hNM hT (le_refl _)
  rw [goldbachG11OrdinaryLevel_eq_low_at_boundary hn δ] at hQ hD hQN
  exact ⟨hB N hNB,hQ,hD,hQN⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig