import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernelLimit
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughConnection

open Finset Set
open scoped BigOperators Interval

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The original closed cross kernel. Repeated primes are retained. -/
def goldbachG12PrimeKernel (h : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ v ∈ goldbachG12Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ)),
    h (Real.log (v.2.2.1 : ℝ) / Real.log (N : ℝ)) * Real.log (N : ℝ) /
      ((goldbachG11LabelProd v : ℝ) * Real.log (v.2.2.2 : ℝ))

/-- The fourth variable has the independent cross interval, not the G11 interval. -/
def goldbachG12PrimeIntegral (h : ℝ → ℝ) : ℝ :=
  ∫ r in (4 / 53 : ℝ)..(4 / 33), ∫ q in r..(4 / 33),
    ∫ s in q..(4 / 33), ∫ t in (4 / 33 : ℝ)..(3 / 11),
      h r / (r * q ^ 2 * s * t)

/-- The cross junction cannot be a prime, by its prime valuation. -/
theorem goldbachG12_prime_ne_cross_cutoff (N p : ℕ) (hp : p.Prime) :
    (p : ℝ) ≠ (N : ℝ) ^ (4 / 33 : ℝ) := by
  intro heq
  have hpow : (p : ℝ) ^ 33 = (N : ℝ) ^ 4 := by
    rw [heq, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have hnat : p ^ 33 = N ^ 4 := by exact_mod_cast hpow
  have hv := congrArg (fun n : ℕ => n.factorization p) hnat
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    hp.factorization_self] at hv
  omega

theorem goldbachG12_prime_cross_cutoff_iff (N p : ℕ) (hp : p.Prime) :
    (N : ℝ) ^ (4 / 33 : ℝ) ≤ (p : ℝ) ↔
      (N : ℝ) ^ (4 / 33 : ℝ) < (p : ℝ) := by
  exact ⟨fun h => lt_of_le_of_ne h (goldbachG12_prime_ne_cross_cutoff N p hp).symm,
    le_of_lt⟩

theorem goldbachG12PrimeKernel_logGeometry {N : ℕ} (hN : 4 ≤ N)
    {v : GoldbachG11Label}
    (hv : v ∈ goldbachG12Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ))) :
    Real.log (v.2.2.1 : ℝ) / Real.log (N : ℝ) ∈ Icc (4 / 53 : ℝ) (4 / 33) ∧
      0 < Real.log (v.2.2.2 : ℝ) := by
  rcases v with ⟨t, s, r, q⟩
  obtain ⟨hr, hq, _, _, _, hl, hrq, hqs, hs, _, _⟩ :=
    mem_goldbachG12Labels_iff.mp hv
  have hrs : (r : ℝ) ≤ s := by exact_mod_cast hrq.trans hqs
  exact ⟨goldbachG12_logPrimeExponent_mem (by omega) hr hl (hrs.trans hs),
    Real.log_pos (by exact_mod_cast hq.one_lt)⟩

theorem goldbachG12PrimeKernel_const (c : ℝ) (N : ℕ) :
    goldbachG12PrimeKernel (fun _ => c) N = c * goldbachG12PrimeKernel (fun _ => 1) N := by
  unfold goldbachG12PrimeKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring


theorem goldbachG12PrimeKernel_nonneg (h : ℝ → ℝ)
    (hh : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    {N : ℕ} (hN : 4 ≤ N) : 0 ≤ goldbachG12PrimeKernel h N := by
  apply sum_nonneg
  intro v hv
  have hg := goldbachG12PrimeKernel_logGeometry hN hv
  exact div_nonneg
    (mul_nonneg (hh _ hg.1) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))))
    (mul_nonneg (Nat.cast_nonneg _) hg.2.le)


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
