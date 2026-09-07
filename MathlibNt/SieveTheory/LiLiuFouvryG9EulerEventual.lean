import MathlibNt.SieveTheory.LiLiuFouvryG9ThirdPrimeEventual
import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedMass

noncomputable section
open Finset Filter
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The true eventual actual-cell Euler bound. The positive product window is
fixed before N0; no extra third-prime witness remains as an input. -/
theorem g9_actual_weighted_euler_eventually {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 →
      ∀ k : ℕ × ℕ × ℕ, (fouvryG9GridCell N e ρ k).Nonempty →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ 2 < p) →
      fouvryG9RectangleEulerMass N ρ k P ≤
        g9BaseEuler P*(1+1/((N : ℝ)^(4/53 : ℝ)/2-2))^3*
          fouvryG9RectangleMass N ρ k := by
  obtain ⟨Nw,hw⟩ := g9_third_prime_eventually_large he
  obtain ⟨Ng,hg⟩ := eventually_atTop.1
    (g9Scale_eventually_const_mul_rpow_le 8 0 (4/53) (by norm_num))
  refine ⟨max Nw (max Ng 1),?_⟩
  intro N hN ρ hρ hρu k hne P hP
  have hNw := (le_max_left _ _).trans hN
  have hrest := (le_max_right _ _).trans hN
  have hNg := (le_max_left _ _).trans hrest
  have hN1 : (1 : ℝ) ≤ N := (le_max_right _ _).trans hrest
  have h8 : 8 ≤ (N : ℝ)^(4/53 : ℝ) := by simpa using hg N hNg
  obtain ⟨_,_,_,hlo,_⟩ := fouvryG9Grid_buffered_geometry he hρ hρu hne
  have hbig : 3 ≤ ρ^k.1 := by linarith
  have hlarge : ∃ y ∈ fouvryG9GridCell N e ρ k,
      (N : ℝ)^(1/3 : ℝ) ≤ ((y.1/y.2.1 : ℕ) : ℝ) := by
    obtain ⟨y,hy⟩ := hne
    exact ⟨y,hy,hw N hNw y (fouvryG9GridCell_mem_iff.mp hy).1⟩
  exact g9_actual_weighted_euler_le_of_large_witness (by exact_mod_cast hN1)
    hρ hρu k hbig hne h8 hlarge P hP

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
