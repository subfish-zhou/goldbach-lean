import MathlibNt.SieveTheory.LiLiuGoldbachG11GridGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG11FouvryRectangle
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9ScaleLevel
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9ModulusSupport

open Finset Filter
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The branch decision belongs to the occupied short cell, not a changed coefficient. -/
def goldbachG11LowGridUsed (N : ℕ) (ε ρ : ℝ) : Finset (ℕ × ℕ) :=
  (goldbachG11GridUsed N ε ρ).filter fun k => ρ^k.1 ≤ (N : ℝ)^(1/10 : ℝ)

def goldbachG11HighGridUsed (N : ℕ) (ε ρ : ℝ) : Finset (ℕ × ℕ) :=
  (goldbachG11GridUsed N ε ρ).filter fun k => ¬ρ^k.1 ≤ (N : ℝ)^(1/10 : ℝ)

/-- The actual original-N level, with the true buffered short scale. -/
def goldbachG11GridLowLevel (N : ℕ) (δ ρ : ℝ) (k : ℕ × ℕ) : ℝ :=
  (N : ℝ)^(5/9-δ)/((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ)

theorem goldbachG11LowGrid_short_upper {N : ℕ} {ε ρ : ℝ} (hρ : 1 < ρ)
    {k : ℕ × ℕ} (hk : k ∈ goldbachG11LowGridUsed N ε ρ) :
    (2/3 : ℝ)*ρ^k.1 ≤ (N : ℝ)^(1/10 : ℝ) := by
  have h := (mem_filter.mp hk).2
  have hT : 0 ≤ ρ^k.1 := pow_nonneg (by linarith) _
  nlinarith

/-- The original-N low level and the physical Fouvry level have the same
signed error for the same supported member. All geometry and the smaller
analytic epsilon are supplied internally from occupied G11 cells. -/
theorem goldbachG11LowGrid_actual_rectangle_error (j A : ℕ) {ε δ : ℝ}
    (hε : 0 < ε) (hεu : ε ≤ 1) (hδ : 0 < δ) (hδu : δ < 1/2) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 →
      ∀ k ∈ goldbachG11LowGridUsed N ε ρ, ∀ c : ℕ → ℝ,
      SignedWellFactorable j (goldbachG11GridLowLevel N δ ρ k) c →
        |signedError (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k)
          (Ioc 0 ⌊goldbachG11GridLowLevel N δ ρ k⌋₊)
          (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
            ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
          (fun p => if p.Coprime N then primeSWBeta p else 0) c N| ≤
          goldbachG11GridPhysicalScale ρ k / Real.log (goldbachG11GridPhysicalScale ρ k)^A := by
  let η : ℝ := min (δ/2) (2/53)
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hηα : η < 4/53 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let Cscale : ℝ := 1/ε
  have hC : 1 ≤ Cscale := (le_div_iff₀ hε).2 (by simpa using hεu)
  have hC0 : 0 < Cscale := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨Ns,hs⟩ := g9Scale_exists_threshold_local_global_and_level
    Cscale η (4/53) δ hC hη hηα (by norm_num) hηδ
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp (goldbachG11_Fouvry_rectangle j A hC hη)
  obtain ⟨Ng,hg⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max Ns (max Ng (max 2 (Cscale*max x₀ 1))),?_⟩
  intro N hN ρ hρ hρu k hk c hc
  obtain ⟨hNs,hrest⟩ := max_le_iff.mp hN
  obtain ⟨hNg,hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hN2,hNlast⟩ := max_le_iff.mp hrest
  have hk0 := (mem_filter.mp hk).1
  have hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ) := hg N hNg
  let z := goldbachG11GridPrimeInterval hρ hρu hbig k hk0
  let M : ℝ := ρ^k.2
  let T : ℝ := (2/3)*ρ^k.1
  let x := goldbachG11GridPhysicalScale ρ k
  let ν := Real.log T / Real.log x
  have hNcx : (N : ℝ) ≤ Cscale*x := goldbachG11GridPhysicalScale_shift hε hρ hρu hk0
  have hNx : (N : ℝ)/Cscale ≤ x :=
    (div_le_iff₀ hC0).2 (by simpa [mul_comm] using hNcx)
  have hxN : x ≤ 4*N := (goldbachG11GridPhysicalScale_window hρ hρu hk0).2
  have hTl : (N : ℝ)^(4/53 : ℝ)/2 ≤ T := goldbachG11Grid_short_scale_lower hρ hρu hk0
  have hTu : T ≤ (N : ℝ)^(1/10 : ℝ) := goldbachG11LowGrid_short_upper hρ hk
  obtain ⟨hx,hT,hid,hlo,hhi,_hNK,hlevel⟩ := hs N hNs x T hNx hxN hTl hTu
  have hQ1 : 1 ≤ goldbachG11GridLowLevel N δ ρ k :=
    g9Scale_global_level_ge_one (by linarith) hT hTu hδu.le
  have hxs : x₀ ≤ x := (le_max_left _ _).trans
    (le_of_mul_le_mul_left (hNlast.trans hNcx) hC0)
  change goldbachG11GridLowLevel N δ ρ k ≤ x^((5-5*ν)/9-η) at hlevel
  have hraw := hx₀ x hxs z M ν (one_le_pow₀ hρ.le) rfl hlo hhi hid
    N (by exact_mod_cast (show (0 : ℝ) < N by linarith)) hNcx
    (goldbachG11GridLong N ε ρ k)
    (fun m hm => goldbachG11GridLong_rectangle hρ hρu k hm) c (hc.level_mono hQ1 hlevel)
  rw [signedError_level_eq_of_support hlevel _ _ _ _ _ _ (hc.factorSupported hQ1)]
  exact hraw

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig