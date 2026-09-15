import Wu08FourMainSupport
import MathlibNt.SieveTheory.LiLiuFouvryG9BaseEuler

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace Wu08FirstPrimeFour.Normalization

/-- Every occupied first-prime cell has a legal actual sqrt cutoff and a level
above a fixed requested threshold. Uniformity precedes xi,rho,e and the cells. -/
theorem occupied_level_gate {δ η : ℝ} (hδ : 0 ≤ δ) (hδu : δ < 1/4)
    (hη : 0 < η) (Q₀ : ℝ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ e : Bool, ∀ ξ ρ : ℝ,
      0 < ξ → 1 < ρ → ρ ≤ 5/4 → ∀ k ∈ occupied N e ξ ρ,
      4 ≤ (N : ℝ) ∧ 4 ≤ (N : ℝ)^truncatedSixthLowerAlpha/2 ∧
      1 ≤ (2/3 : ℝ)*ρ^k.1 ∧ 1 ≤ level N ρ δ k ∧ Q₀ ≤ level N ρ δ k ∧
      level N ρ δ k ≤ N ∧ 2 ≤ sqrt (N : ℝ) ∧ sqrt (N : ℝ) ≤ (level N ρ δ k)^2 := by
  obtain ⟨Nw,hw⟩ := g9WF_exists_internal_level_gate hδ (by linarith) hη Q₀
  obtain ⟨Ng,hg⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 8 0 truncatedSixthLowerAlpha
      (by norm_num [truncatedSixthLowerAlpha]))
  refine ⟨max 4 (max Nw Ng),?_⟩
  intro N hN e ξ ρ hξ hρ hρu k hk
  have hN4 : (4 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hnw := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hng := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hbig : (8 : ℝ) ≤ (N : ℝ)^truncatedSixthLowerAlpha := by simpa using hg N hng
  obtain ⟨_,_,_,hTlo,hThi⟩ := occupied_geometry hξ hρ hρu hk
  have hT : 1 ≤ (2/3 : ℝ)*ρ^k.1 := by linarith
  obtain ⟨_,hQ1,hQ,_,hQN⟩ := hw N _ hnw hT hThi
  obtain ⟨hz,hzQ⟩ := g9WF_sqrt_cutoff hN4 hT hThi hδ hδu
  exact ⟨hN4,by linarith,hT,hQ1,hQ,hQN,hz,hzQ⟩

/-- Full actual main-term evaluation, NOT just an Euler identity. The result
retains its real cell masses and all analytic sieve defects explicitly. -/
theorem properMain_density_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 1 < K ∧
    ∀ δ η : ℝ, 0 ≤ δ → δ < 1/4 → 0 < η → η < 1/8 →
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
    ∀ e : Bool, ∀ ξ ρ : ℝ, 0 < ξ → 1 < ρ → ρ ≤ 5/4 →
      (∀ k ∈ occupied N e ξ ρ, 0 ≤ fouvryG9UpperFactor N (level N ρ δ k) C K η) ∧
      properMain N e ξ ρ δ η ≤
        fouvryG9BaseEuler N (sqrt N)*fullEulerCorrection N*
          (∑ k ∈ occupied N e ξ ρ,
            fouvryG9UpperFactor N (level N ρ δ k) C K η*cellMass N e ξ ρ k) := by
  obtain ⟨C,hC,K,hK,hden⟩ := g9ProgressionDensity_upper
  refine ⟨C,hC,K,hK,?_⟩
  intro δ η hδ hδu hη hηu
  obtain ⟨Q₀,hQ₀,hupper⟩ := hden η hη hηu
  obtain ⟨Ng,hg⟩ := occupied_level_gate hδ hδu hη Q₀
  refine ⟨Ng,?_⟩
  intro N hN hEven e ξ ρ hξ hρ hρu
  have hlocal : ∀ k ∈ occupied N e ξ ρ,
      0 ≤ fouvryG9UpperFactor N (level N ρ δ k) C K η ∧
      cellMain N e ξ ρ δ η (sqrt N) (properPrimes N) k ≤
        fouvryG9BaseEuler N (sqrt N)*fullEulerCorrection N*
          (fouvryG9UpperFactor N (level N ρ δ k) C K η*cellMass N e ξ ρ k) := by
    intro k hk
    obtain ⟨hN4,hbig,_,_,hQ,hQN,hz,hzQ⟩ := hg N hN e ξ ρ hξ hρ hρu k hk
    have hq4 : 4 ≤ level N ρ δ k := hQ₀.trans hQ
    have hlq : 0 < log (level N ρ δ k) := log_pos (by linarith)
    have hlz : 0 < log (sqrt (N : ℝ)) := log_pos (by linarith)
    have hcoord : log (level N ρ δ k)/log (sqrt N) ≤ 3 := by
      apply (div_le_iff₀ hlz).mpr
      rw [log_sqrt (Nat.cast_nonneg N)]
      have hlog := log_le_log (by linarith : 0 < level N ρ δ k) hQN
      have hln : 0 ≤ log (N : ℝ) := log_nonneg (by linarith)
      linarith
    have hf : 0 ≤ fouvryG9UpperFactor N (level N ρ δ k) C K η := by
      unfold fouvryG9UpperFactor
      rw [jr1965F_eq_of_le_three hcoord]
      positivity
    refine ⟨hf,?_⟩
    have heuler := cell_euler_upper hξ hρ hρu hEven hbig hk
    have hmain : cellMain N e ξ ρ δ η (sqrt N) (properPrimes N) k ≤
        fouvryG9UpperFactor N (level N ρ δ k) C K η*
          (∑ m ∈ products (longCell N e ξ ρ k), ∑ a ∈ shortCell ρ k,
            alpha (longCell N e ξ ρ k) m*beta N a*
              (∏ p ∈ properPrimes N, (1-progressionDensity (m*a) p))) := by
      unfold cellMain
      simp only [mul_sum]
      apply sum_le_sum
      intro m _
      apply sum_le_sum
      intro a _
      have hh := hupper (level N ρ δ k) hQ (m*a) (properPrimes N)
        (fouvryG9SievePrimes_odd hEven _) (sqrt N) hz hzQ
        (fun p hp => (fouvryG9SievePrimes_mem N p _ |>.mp hp).2.2)
      exact (mul_le_mul_of_nonneg_left hh
        (mul_nonneg (alpha_nonneg _ _) (beta_nonneg _ _))).trans_eq (by unfold fouvryG9UpperFactor; ring)
    exact (hmain.trans (mul_le_mul_of_nonneg_left heuler hf)).trans_eq (by
      change _ = g9BaseEuler (properPrimes N)*fullEulerCorrection N*_
      ring)
  refine ⟨fun k hk => (hlocal k hk).1,?_⟩
  unfold properMain
  rw [mul_sum]
  exact sum_le_sum (fun k hk => (hlocal k hk).2)

/-- The REAL full-cofactor loss tends to one, uniformly before every cell. -/
theorem fullEulerCorrection_eventually {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → fullEulerCorrection N ≤ 1+ζ := by
  have hd : Tendsto (fun x : ℝ => x^truncatedSixthLowerAlpha/2-2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_rpow_atTop (by norm_num [truncatedSixthLowerAlpha] :
      0 < truncatedSixthLowerAlpha)).eventually (eventually_ge_atTop (2*(b+2)))] with x hx
    linarith
  have hi := tendsto_inv_atTop_zero.comp hd
  have ht : Tendsto (fun x : ℝ => (1+1/(x^truncatedSixthLowerAlpha/2-2))^21) atTop (nhds 1) := by
    simpa only [one_div,add_zero,one_pow,Function.comp_apply] using (hi.const_add 1).pow 21
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (show (1 : ℝ) < 1+ζ by linarith)))
  exact ⟨M,fun N hN => (hM N hN).le⟩

#print axioms properMain_density_upper
#print axioms fullEulerCorrection_eventually
end Wu08FirstPrimeFour.Normalization
