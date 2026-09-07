import MathlibNt.SieveTheory.LiLiuFouvryG9ProductFibreActual
import MathlibNt.SieveTheory.LiLiuFouvryG9RectangleSieve
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9BufferedScale
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9ShortInterval
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTauPointwise

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual enlarged rectangle has uniformly bounded integer differences. -/
theorem fouvryG9RemainderMajorant_support {N : ℕ} {e ρ : ℝ}
    (he : 0 < e) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    {k : ℕ × ℕ × ℕ} (hbig : 3 ≤ ρ^k.1)
    (hne : (fouvryG9GridCell N e ρ k).Nonempty)
    {p : ℕ × ℕ}
    (hp : p ∈ fouvryG9LongProducts N ρ k ×ˢ fouvryG9RectanglePrimeSupport N ρ k) :
    ((N : ℤ) - (p.1 : ℤ)*p.2).natAbs ≤ 4*N := by
  obtain ⟨hm, hn⟩ := mem_product.mp hp
  have hm' := fouvryG9LongProducts_le_two hρ hρu hm
  let z := fouvryG9GridPrimeInterval hρ hρu k hbig hne
  have hn' := (primeC2Interval_support z p.2 hn).2
  change (p.2 : ℝ) ≤ 2*((2/3 : ℝ)*ρ^k.1) at hn'
  have hg := (fouvryG9Grid_buffered_geometry he hρ hρu hne).2.2.1
  have hprod : (p.1 : ℝ)*p.2 ≤ 4*(N : ℝ) := by
    have hh := mul_le_mul hm' hn' (Nat.cast_nonneg p.2)
      (by positivity : 0 ≤ 2*ρ^(k.2.1+k.2.2))
    nlinarith only [hh, hg]
  have hpN : p.1*p.2 ≤ 4*N := by exact_mod_cast hprod
  omega

/-- Fixed-exponent uniform fiber constant, with the zero product handled by τ(0)=0. -/
theorem fouvryG9RemainderMajorant_fibres {κ : ℝ} (hκ : 0 < κ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ)
      (U V : Finset ℕ) (r : ℕ), r ≤ 4*N →
      (∑ p ∈ U ×ˢ V, if ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs = r then
        fouvryG9LongAlpha N ρ k p.1*fouvryG9RectangleBeta N p.2 else 0)
        ≤ 2*C₀*(5*(N : ℝ))^κ := by
  obtain ⟨C₀,hC₀,hτ⟩ := fouvryTau_le_const_rpow (k := 3) (by norm_num) hκ
  refine ⟨C₀,hC₀,?_⟩
  intro N ρ k U V r hr
  have hb : ∀ v : ℕ, v ≤ 5*N → (fouvryTau 3 v : ℝ) ≤ C₀*(5*(N : ℝ))^κ := by
    intro v hv
    by_cases hv0 : v = 0
    · subst v
      simp only [fouvryTau, ArithmeticFunction.map_zero, Nat.cast_zero]
      positivity
    · exact (hτ v (Nat.pos_of_ne_zero hv0)).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg v) (by exact_mod_cast hv) hκ.le) hC₀.le)
  have h1 := hb (N+r) (by omega)
  have h2 := hb (N-r) (by omega)
  have hf := fouvryG9Long_prime_natAbs_fibre_le N ρ k U V r
  change (∑ p ∈ U ×ˢ V, if ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs = r then
    fouvryG9LongAlpha N ρ k p.1*fouvryG9RectangleBeta N p.2 else 0) ≤ _ at hf
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
