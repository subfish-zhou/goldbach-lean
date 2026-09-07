import MathlibNt.SieveTheory.LiLiuGoldbachClosedTriples
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped BigOperators
open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem TotientCorrection_prime_cast (p : ℕ) (hp : p.Prime) :
    (p.totient : ℝ) = (p : ℝ) - 1 := by
  simp only [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]

/-- The omitted term in replacing 1/phi(p) by 1/p is retained exactly.
Weights need not be positive for this identity. -/
theorem goldbachPrime_totient_weighted_correction
    (s : Finset ℕ) (w : ℕ → ℝ) (hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, w p / (p.totient : ℝ)) =
      (∑ p ∈ s, w p / (p : ℝ)) +
        ∑ p ∈ s, w p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpr : (1 : ℝ) < p := by exact_mod_cast (hs p hp).one_lt
  rw [TotientCorrection_prime_cast p (hs p hp)]
  field_simp [ne_of_gt (show (0 : ℝ) < p by linarith), ne_of_gt (sub_pos.mpr hpr)]
  ring

/-- Uniform relative payment of the positive correction, valid for every
nonnegative weight on the actual finite set of primes above Z. -/
theorem goldbachPrime_totient_weighted_le
    (s : Finset ℕ) (w : ℕ → ℝ) (Z : ℝ) (hZ : 1 < Z)
    (hs : ∀ p ∈ s, p.Prime ∧ Z ≤ (p : ℝ)) (hw : ∀ p ∈ s, 0 ≤ w p) :
    (∑ p ∈ s, w p / (p.totient : ℝ)) ≤
      (1 + 1 / (Z - 1)) * ∑ p ∈ s, w p / (p : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpr : (1 : ℝ) < p := hZ.trans_le (hs p hp).2
  have hp0 : (0 : ℝ) < p := by linarith
  have hrec : 1 / ((p : ℝ) - 1) ≤ 1 / (Z - 1) :=
    one_div_le_one_div_of_le (sub_pos.mpr hZ) (sub_le_sub_right (hs p hp).2 1)
  have hmul := mul_le_mul_of_nonneg_left hrec (div_nonneg (hw p hp) hp0.le)
  have heq : w p / (p.totient : ℝ) =
      w p / (p : ℝ) + (w p / (p : ℝ)) * (1 / ((p : ℝ) - 1)) := by
    rw [TotientCorrection_prime_cast p (hs p hp).1]
    field_simp [hp0.ne', (sub_pos.mpr hpr).ne']
    ring
  rw [heq]
  nlinarith

/-- The N threshold is chosen before the finite prime set and its weights;
therefore it applies to kernels and supports varying with N. -/
theorem goldbachPrime_totient_weighted_rpow_eventually
    (α η : ℝ) (hα : 0 < α) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (s : Finset ℕ) (w : ℕ → ℝ),
        (∀ p ∈ s, p.Prime ∧ (N : ℝ) ^ α ≤ (p : ℝ)) →
        (∀ p ∈ s, 0 ≤ w p) →
        (∑ p ∈ s, w p / (p.totient : ℝ)) ≤
          (1 + η) * ∑ p ∈ s, w p / (p : ℝ) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (1 + 1 / η)))
  refine ⟨max 2 N₁, le_max_left _ _, ?_⟩
  intro N hN s w hs hw
  have hlarge : 1 + 1 / η ≤ (N : ℝ) ^ α := hN₁ N ((le_max_right _ _).trans hN)
  have hZ : 1 < (N : ℝ) ^ α := by linarith [one_div_pos.mpr hη]
  have hrec : 1 / ((N : ℝ) ^ α - 1) ≤ η := by
    apply (div_le_iff₀ (sub_pos.mpr hZ)).2
    have hh := (div_le_iff₀ hη).mp (show 1 / η ≤ (N : ℝ) ^ α - 1 by linarith)
    nlinarith
  have hsum : 0 ≤ ∑ p ∈ s, w p / (p : ℝ) :=
    Finset.sum_nonneg (fun p hp => div_nonneg (hw p hp) (Nat.cast_nonneg p))
  have hm := mul_le_mul_of_nonneg_right (show 1 + 1 / ((N : ℝ) ^ α - 1) ≤ 1 + η by linarith) hsum
  exact (goldbachPrime_totient_weighted_le s w ((N : ℝ) ^ α) hZ hs hw).trans hm

/-- Specialization to the actual closed S3 outer prime carrier, uniformly in
its upper endpoint and in the nonnegative kernel. -/
theorem goldbachS3PrimeWeights_totient_upper_eventually
    (α η : ℝ) (hα : 0 < α) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (y : ℝ) (w : ℕ → ℝ),
        (∀ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ α) y, 0 ≤ w p) →
        (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ α) y, w p / (p.totient : ℝ)) ≤
          (1 + η) * ∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ α) y, w p / (p : ℝ) := by
  obtain ⟨N₀, hN₀, hN⟩ := goldbachPrime_totient_weighted_rpow_eventually α η hα hη
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN y w hw
  apply hN N hNN _ w _ hw
  intro p hp
  rcases mem_goldbachClosedPrimes_iff.mp hp with ⟨hprime, _, hlower, _⟩
  exact ⟨hprime, hlower⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig