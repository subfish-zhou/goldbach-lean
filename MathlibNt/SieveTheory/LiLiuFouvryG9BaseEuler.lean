import MathlibNt.SieveTheory.LiLiuFouvryG9MainUpper
import MathlibNt.SieveTheory.LiLiuGoldbachB10SieveProduct

noncomputable section
open Finset
open MathlibNt.SieveTheory
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The base Euler product uses the exact strict prime cutoff and actual N. -/
def fouvryG9BaseEuler (N : ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ fouvryG9SievePrimes N z, (1-1/((p : ℝ)-1))

/-- Exact reuse of the already accepted B10/Mertens product normalization. -/
theorem fouvryG9BaseEuler_eq_B10 (N : ℕ) (z : ℝ) :
    fouvryG9BaseEuler N z = goldbachB10PrimeProduct N z := by
  unfold fouvryG9BaseEuler goldbachB10PrimeProduct MertensTheorem.goldbachSieveProduct
  apply prod_congr _ (fun _ _ => rfl)
  ext p
  simp only [fouvryG9SievePrimes,mem_filter,mem_range]
  constructor
  · rintro ⟨hb,hp,hc⟩
    exact ⟨hb,hp,hp.coprime_iff_not_dvd.mp hc⟩
  · rintro ⟨hb,hp,hn⟩
    exact ⟨hb,hp,hp.coprime_iff_not_dvd.mpr hn⟩

/-- Uniform Liu singular-series normalization, with the full prime-divisor
correction for N supplied by the existing Mertens theorem. -/
theorem fouvryG9BaseEuler_log_upper (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧ ∀ N : ℕ, 4 ≤ N → Even N → ∀ z : ℝ, z₀ ≤ z →
      fouvryG9BaseEuler N z*Real.log z ≤
        2*Real.exp (-Real.eulerMascheroniConstant)*(1+ζ)*SingularSeries.liuSingularSeries N := by
  simpa only [fouvryG9BaseEuler_eq_B10] using
    goldbachB10PrimeProduct_log_le_liuSingularSeries ζ hζ

/-- The sqrt(N) specialization, with threshold still before the changing N. -/
theorem fouvryG9BaseEuler_sqrt_upper (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      fouvryG9BaseEuler N (Real.sqrt N)*Real.log (N : ℝ) ≤
        4*Real.exp (-Real.eulerMascheroniConstant)*(1+ζ)*SingularSeries.liuSingularSeries N := by
  obtain ⟨z₀,hz₀,hbound⟩ := fouvryG9BaseEuler_log_upper ζ hζ
  refine ⟨max 4 (z₀^2),?_⟩
  intro N hN hEven
  have hN4 : (4 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hzN : z₀^2 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hz : z₀ ≤ Real.sqrt N := by
    nlinarith [Real.sq_sqrt hN0, Real.sqrt_nonneg (N : ℝ)]
  have h := hbound N (by exact_mod_cast hN4) hEven (Real.sqrt N) hz
  rw [Real.log_sqrt hN0] at h
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
