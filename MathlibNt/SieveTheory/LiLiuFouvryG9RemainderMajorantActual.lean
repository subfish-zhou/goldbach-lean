import MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantDiscrepancy

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Uniform inverse-totient majorant for the actual G9 remainder.
The positive constant is selected before N, the grid, the cell and the modulus.
The only assumptions are the stated geometric conditions and 0 < d ≤ N. -/
theorem fouvryG9RemainderMajorant_actual {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ e ρ : ℝ, 0 < e → 1 < ρ → ρ ≤ 5/4 →
      ∀ k : ℕ × ℕ × ℕ, (fouvryG9GridCell N e ρ k).Nonempty → 3 ≤ ρ^k.1 →
      ∀ d : ℕ, 0 < d → d ≤ N →
      |bilinearDiscrepancy
        (fouvryG9LongProducts N ρ k) (fouvryG9RectanglePrimeSupport N ρ k)
        (fouvryG9LongAlpha N ρ k) (fouvryG9RectangleBeta N) N d|
        ≤ C*(N : ℝ)^(1+κ)/(d.totient : ℝ) := by
  obtain ⟨C₀,hC₀,hfib⟩ := fouvryG9RemainderMajorant_fibres hκ
  refine ⟨20*C₀*(5 : ℝ)^κ, by positivity, ?_⟩
  intro N hN e ρ he hρ hρu k hne hbig d hd hdN
  let J := 2*C₀*(5*(N : ℝ))^κ
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have h := fouvryG9RemainderMajorant_discrepancy
    (fouvryG9LongProducts N ρ k) (fouvryG9RectanglePrimeSupport N ρ k)
    (fouvryG9LongAlpha N ρ k) (fouvryG9RectangleBeta N) N hN J hJ
    (fun p _ => mul_nonneg (fouvryG9LongAlpha_nonneg N ρ k p.1)
      (fouvryG9_prime_copN_beta_bounds N p.2).1)
    (fun _ hp => fouvryG9RemainderMajorant_support he hρ hρu hbig hne hp)
    (hfib N ρ k _ _) d hd hdN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  convert h using 1
  dsimp [J]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hN0.le,
    Real.rpow_add hN0, Real.rpow_one]
  ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
