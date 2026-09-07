import MathlibNt.SieveTheory.LiLiuGoldbachG11LowGridCost
import MathlibNt.SieveTheory.LiLiuFouvryG9WFLevel

open Finset Filter
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The full same-member signed errors over actual low cells and actual external tags. -/
def goldbachG11LowGridFamilyError (N : ℕ) (ε δ θ ρ : ℝ)
    (P : (ℕ × ℕ) → Finset ℕ) (z : (ℕ × ℕ) → ℝ) : ℝ :=
  ∑ k ∈ goldbachG11LowGridUsed N ε ρ,
    ∑ t ∈ externalTags true (P k) (externalInternalLevel (goldbachG11GridLowLevel N δ ρ k) θ) θ (z k),
      |signedError (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k)
        (Ioc 0 ⌊goldbachG11GridLowLevel N δ ρ k⌋₊)
        (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
          ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
        (fun p => if p.Coprime N then primeSWBeta p else 0)
        (fun d => externalTerm true (P k)
          (externalInternalLevel (goldbachG11GridLowLevel N δ ρ k) θ) θ (z k) t d) N|

/-- Fully paid low-grid distribution error. The threshold precedes all changing
sieve carriers, cutoffs, cells and members. No SW, WF, cardinality, mass or
per-cell-error hypothesis remains; fixed rho and epsilon dependence is retained. -/
theorem goldbachG11LowGrid_externalFamily_error_total (A : ℕ) {ε δ θ ρ : ℝ}
    (hε : 0 < ε) (hεu : ε ≤ 1) (hδ : 0 < δ) (hδu : δ < 1/2)
    (hθ : 0 < θ) (hθu : θ < 1/8) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ (P : (ℕ × ℕ) → Finset ℕ) (z : (ℕ × ℕ) → ℝ),
        goldbachG11LowGridFamilyError N ε δ θ ρ P z ≤ (N : ℝ)/Real.log (N : ℝ)^A := by
  let Kscale : ℝ := 1/ε
  have hK : 1 ≤ Kscale := (le_div_iff₀ hε).2 (by simpa using hεu)
  have hK0 : 0 < Kscale := lt_of_lt_of_le zero_lt_one hK
  let B : ℝ := Real.exp (8*(θ⁻¹)^3)
  let C : ℝ := 4*2^(A+4)
  let D : ℝ := (1/Real.log ρ+1)^3
  let L : ℝ := max 1 (max (2*Real.log Kscale) (D*(B*C)))
  obtain ⟨Ns,hs⟩ := goldbachG11LowGrid_actual_rectangle_error 1 (A+4) hε hεu hδ hδu
  obtain ⟨Ng,hg⟩ := g9WF_exists_internal_level_gate hδ.le hδu hθ 1
  obtain ⟨Nr,hr⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).eventually
      (eventually_ge_atTop (2 : ℝ)))
  refine ⟨max Ns (max Ng (max Nr (Real.exp L))),?_⟩
  intro N hN P z
  obtain ⟨hNs,hrest⟩ := max_le_iff.mp hN
  obtain ⟨hNg,hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hNr,hNexp⟩ := max_le_iff.mp hrest
  have hn : (0 : ℝ) < N := (Real.exp_pos L).trans_le hNexp
  have hL : L ≤ Real.log (N : ℝ) := (Real.le_log_iff_exp_le hn).2 hNexp
  have hlog : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL
  have hlpos : 0 < Real.log (N : ℝ) := by linarith
  have hlarge : 2*Real.log Kscale ≤ Real.log (N : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hL
  have hDC : D*(B*C) ≤ Real.log (N : ℝ) :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hL
  let I := fun k => externalTags true (P k)
    (externalInternalLevel (goldbachG11GridLowLevel N δ ρ k) θ) θ (z k)
  let E := fun (k : ℕ × ℕ) t =>
    signedError (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k)
      (Ioc 0 ⌊goldbachG11GridLowLevel N δ ρ k⌋₊)
      (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
      (fun p => if p.Coprime N then primeSWBeta p else 0)
      (fun d => externalTerm true (P k)
        (externalInternalLevel (goldbachG11GridLowLevel N δ ρ k) θ) θ (z k) t d) N
  have hcell : ∀ k ∈ goldbachG11LowGridUsed N ε ρ,
      (∑ t ∈ I k, |E k t|) ≤ B*(C*N/Real.log (N : ℝ)^(A+4)) := by
    intro k hk
    have hk0 := (mem_filter.mp hk).1
    let T : ℝ := (2/3)*ρ^k.1
    have hTlo := goldbachG11Grid_short_scale_lower hρ hρu hk0
    have hT : 1 ≤ T := by dsimp [T]; linarith [hr N hNr]
    have hTu : T ≤ (N : ℝ)^(1/10 : ℝ) := goldbachG11LowGrid_short_upper hρ hk
    obtain ⟨_hN1,hQ1,_hQ0,hD,_hQN⟩ := hg N T hNg hT hTu
    have hc : ((I k).card : ℝ) ≤ B :=
      (externalTags_card_and_wellFactorable true (P k) (z k) hD hθ hθu).1.le
    have hlocal : ∀ t ∈ I k, |E k t| ≤ C*N/Real.log (N : ℝ)^(A+4) := by
      intro t ht
      have hWF := externalTerm_signedWellFactorable true (P k) (z k) t
        (zero_le_one.trans hQ1) hD hθ hθu ht
      have hraw := hs N hNs ρ hρ hρu k hk _ hWF
      have hNcx := goldbachG11GridPhysicalScale_shift hε hρ hρu hk0
      have hxlo : (N : ℝ)/Kscale ≤ goldbachG11GridPhysicalScale ρ k :=
        (div_le_iff₀ hK0).2 (by simpa [Kscale, mul_comm] using hNcx)
      exact fouvryG9GridCost_one A hK hn hlog hlarge hxlo
        (goldbachG11GridPhysicalScale_window hρ hρu hk0).2 hraw
    have hh := sum_le_sum hlocal
    simp only [sum_const, nsmul_eq_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hc (by dsimp [C]; positivity))
  have htotal := sum_le_sum hcell
  simp only [sum_const, nsmul_eq_mul] at htotal
  have hcard : ((goldbachG11LowGridUsed N ε ρ).card : ℝ) ≤ D*Real.log (N : ℝ)^3 :=
    goldbachG11LowGridCost_card hρ hlog
  change (∑ k ∈ goldbachG11LowGridUsed N ε ρ, ∑ t ∈ I k, |E k t|) ≤ _
  calc
    _ ≤ ((goldbachG11LowGridUsed N ε ρ).card : ℝ)*(B*(C*N/Real.log (N : ℝ)^(A+4))) := htotal
    _ ≤ (D*Real.log (N : ℝ)^3)*(B*(C*N/Real.log (N : ℝ)^(A+4))) :=
      mul_le_mul_of_nonneg_right hcard (by dsimp [B,C]; positivity)
    _ = (D*Real.log (N : ℝ)^3)*((B*C)*N/Real.log (N : ℝ)^(A+4)) := by ring
    _ ≤ _ := fouvryG9GridCost_scalar A hn.le hlpos hDC

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig