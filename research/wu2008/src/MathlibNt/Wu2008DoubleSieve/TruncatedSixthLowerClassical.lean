import MathlibNt.Wu2008DoubleSieve.TruncatedSixthLowerPrimeGeometry

/-!
# The actual masked classical count with its AP errors paid

This theorem includes the high-prime wedge. Its main term is still the
literal reciprocal-totient prime sum, not a polygon integral.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

noncomputable def truncatedSixthLowerClassicalMain (N : ℕ) (δ ρ : ℝ)
    (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ t ∈ S, (logarithmicIntegral N / (Nat.totient (t.1 * t.2) : ℝ)) *
    ((jr1965f (truncatedSixthLowerPrimeS N δ t) - ρ) *
      localSieveProduct N ((N : ℝ) ^ truncatedSixthLowerAlpha))

theorem truncatedSixthLower_classical_masked {δ ρ A : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ S : Finset (ℕ × ℕ), S ⊆ truncatedSixthLowerPairs N δ →
        truncatedSixthLowerClassicalMain N δ ρ S - C * (N : ℝ) / log N ^ A ≤
          ∑ t ∈ S, (sieveCount N (t.1 * t.2) N
            ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨z0, hlower⟩ := truncatedSixthLower_pair_signed hρ
  obtain ⟨C, hC, T1, hAP⟩ :=
    truncatedSixthLower_masked_AP_uniform truncatedSixthLower_parameters.1 hδ hA
  have hz := ((tendsto_rpow_atTop truncatedSixthLower_parameters.1).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (max z0 2))
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp hz
  refine ⟨C, hC, max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N hN he S hS
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 < N := by omega
  have hNT1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNT2 : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hz0 := (le_max_left z0 2).trans (hT2 N hNT2)
  have hz2 := (le_max_right z0 2).trans (hT2 N hNT2)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNW : (N : ℝ) ^ truncatedSixthLowerAlpha ≤ (N : ℝ) ^ truncatedSixthLowerBeta :=
    rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1.le)
      truncatedSixthLower_parameters.2.1.le
  have hrect : S ⊆ primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha)
      ((N : ℝ) ^ truncatedSixthLowerBeta) ×ˢ
      primeWindow N ((N : ℝ) ^ truncatedSixthLowerBeta)
        ((N : ℝ) ^ truncatedSixthLowerSigma) :=
    fun t ht => (mem_filter.mp (hS ht)).1
  have herr := hAP N hNT1 _ _
    (fun p hp => let h := mem_primeWindow.mp hp; ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun q hq => let h := mem_primeWindow.mp hq; ⟨h.1, h.2.1, hNW.trans h.2.2.1⟩)
    S hrect ((N : ℝ) ^ truncatedSixthLowerAlpha)
  have hpoint : ∀ t ∈ S,
      (logarithmicIntegral N / (Nat.totient (t.1 * t.2) : ℝ)) *
        ((jr1965f (truncatedSixthLowerPrimeS N δ t) - ρ) *
          localSieveProduct N ((N : ℝ) ^ truncatedSixthLowerAlpha)) ≤
      (sieveCount N (t.1 * t.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) +
        |ordinaryRosserRemainder false N (t.1 * t.2)
          (⌊(N : ℝ) ^ (1 / 2 - δ) / (t.1 * t.2 : ℕ)⌋₊ + 1)
          ((N : ℝ) ^ truncatedSixthLowerAlpha)| := by
    intro t ht
    obtain ⟨hp, hq⟩ := mem_product.mp (hrect ht)
    have hp' := mem_primeWindow.mp hp
    have hq' := mem_primeWindow.mp hq
    have hprod : (0 : ℝ) < (t.1 * t.2 : ℕ) := by
      exact_mod_cast mul_pos hp'.1.pos hq'.1.pos
    have hs := truncatedSixthLower_prime_s_bounds hN1 hδ.le (hS ht)
    have h := hlower N t.1 t.2 he (by omega) hp'.1 hq'.1
      ((N : ℝ) ^ truncatedSixthLowerAlpha)
      ((N : ℝ) ^ truncatedSixthLowerC δ / (t.1 * t.2 : ℕ))
      (truncatedSixthLowerPrimeS N δ t) hp'.2.2.1 (hNW.trans hq'.2.2.1)
      hz0 hz2 (div_pos (rpow_pos_of_pos hN0 _) hprod) rfl hs.1 (by linarith [hs.2])
    have hr := neg_abs_le (ordinaryRosserRemainder false N (t.1 * t.2)
      (⌊(N : ℝ) ^ (1 / 2 - δ) / (t.1 * t.2 : ℕ)⌋₊ + 1)
      ((N : ℝ) ^ truncatedSixthLowerAlpha))
    change _ + ordinaryRosserRemainder false N (t.1 * t.2)
      (⌊(N : ℝ) ^ (1 / 2 - δ) / (t.1 * t.2 : ℕ)⌋₊ + 1)
      ((N : ℝ) ^ truncatedSixthLowerAlpha) ≤ _ at h
    linarith
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib] at hsum
  unfold truncatedSixthLowerClassicalMain
  linarith

theorem truncatedSixthLower_classical_actual_mass {δ ρ A : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthLowerClassicalMain N δ ρ (truncatedSixthLowerPairs N δ) -
        C * (N : ℝ) / log N ^ A ≤
      (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
        ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
        ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨C, hC, T, hT, h⟩ := truncatedSixthLower_classical_masked hδ hρ hA
  refine ⟨C, hC, T, hT, ?_⟩
  intro N hN he
  apply (h N hN he _ subset_rfl).trans
  unfold truncatedSixthMass
  push_cast
  apply sum_le_sum_of_subset_of_nonneg (truncatedSixthLower_pairs_subset (by omega) hδ)
  intro t _ _
  exact_mod_cast (show (0 : ℤ) ≤ sieveCount N (t.1 * t.2) N
    ((N : ℝ) ^ truncatedSixthLowerAlpha) from Int.natCast_nonneg _)

end Wu2008DoubleSieve
