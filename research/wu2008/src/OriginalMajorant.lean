import OriginalSieve
import MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantDiscrepancy
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTauPointwise

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace OriginalU8

/-- True divisor convolution, retaining all ordered labels and their diagonal.
No prime-product bounded-multiplicity assumption is used. -/
theorem original_natAbs_fibre (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ)
    (U V : Finset ℕ) (r : ℕ) :
    (∑ p ∈ U ×ˢ V, if ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs = r then
      alpha (labels N ρ k) p.1 * beta N p.2 else 0) ≤
      (fouvryTau 3 (N+r) : ℝ) + (fouvryTau 3 (N-r) : ℝ) := by
  apply fouvryG9_weighted_natAbs_fibre_le
  · intro m _
    exact ⟨alpha_nonneg _ _, (le_abs_self _).trans
      (alpha_order_two _ (labels_positive N ρ k) m)⟩
  · intro n _
    exact fouvryG9_prime_copN_beta_bounds N n

/-- Whole-rectangle support: integer absolute differences include zero and overhang. -/
theorem original_output_support {N : ℕ} {e ρ : ℝ}
    (he : 0 < e) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    {k : ℕ × ℕ × ℕ} (hbig : 3 ≤ ρ^k.1) (hne : Occupied N e ρ k)
    {p : ℕ × ℕ} (hp : p ∈ products (labels N ρ k) ×ˢ primeSupport N ρ k) :
    ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs ≤ 4*N := by
  obtain ⟨hm,hn⟩ := mem_product.mp hp
  have hm' := (products_bounds hρ hρu hm).2
  have hn' := (primeSupport_mem hρ hρu k hbig hne p.2).mp hn
  have hnup : (p.2 : ℝ) ≤ 2*((2/3 : ℝ)*ρ^k.1) := by
    have hh := hn'.2.2.1
    rw [pow_succ] at hh
    have hpow := pow_pos (show 0 < ρ by linarith) k.1
    nlinarith
  have hg := (geometry he hρ hρu hne).2.2.1
  have hprod : (p.1 : ℝ)*p.2 ≤ 4*(N : ℝ) := by
    have hh := mul_le_mul hm' hnup (Nat.cast_nonneg p.2)
      (by positivity : 0 ≤ 2*ρ^(k.2.1+k.2.2))
    nlinarith only [hh,hg]
  have hpN : p.1*p.2 ≤ 4*N := by exact_mod_cast hprod
  omega

/-- Uniform actual fibers from the proved tau-three pointwise theorem. -/
theorem original_fibres {κ : ℝ} (hκ : 0 < κ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ)
      (U V : Finset ℕ) (r : ℕ), r ≤ 4*N →
      (∑ p ∈ U ×ˢ V, if ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs = r then
        alpha (labels N ρ k) p.1*beta N p.2 else 0) ≤ 2*C₀*(5*(N : ℝ))^κ := by
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
  have hf := original_natAbs_fibre N ρ k U V r
  linarith

/-- The local inverse-totient majorant is proved, not an input `hr`.
The constant is uniform in all occupied rectangles, including rho approaching one. -/
theorem original_discrepancy_majorant {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ e ρ : ℝ, 0 < e → 1 < ρ → ρ ≤ 5/4 →
      ∀ k : ℕ × ℕ × ℕ, Occupied N e ρ k → 3 ≤ ρ^k.1 →
      ∀ d : ℕ, 0 < d → d ≤ N →
      |discrepancy N ρ k d| ≤ C*(N : ℝ)^(1+κ)/(d.totient : ℝ) := by
  obtain ⟨C₀,hC₀,hfib⟩ := original_fibres hκ
  refine ⟨20*C₀*(5 : ℝ)^κ, by positivity, ?_⟩
  intro N hN e ρ he hρ hρu k hne hbig d hd hdN
  let J := 2*C₀*(5*(N : ℝ))^κ
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have h := fouvryG9RemainderMajorant_discrepancy
    (products (labels N ρ k)) (primeSupport N ρ k)
    (alpha (labels N ρ k)) (beta N) N hN J hJ
    (fun p _ => mul_nonneg (alpha_nonneg _ _) (fouvryG9_prime_copN_beta_bounds N p.2).1)
    (fun _ hp => original_output_support he hρ hρu hbig hne hp)
    (hfib N ρ k _ _) d hd hdN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  change |discrepancy N ρ k d| ≤ _ at h
  convert h using 1
  dsimp [J]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hN0.le,
    Real.rpow_add hN0, Real.rpow_one]
  ring

end OriginalU8
