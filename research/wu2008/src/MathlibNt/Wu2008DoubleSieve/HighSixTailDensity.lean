import MathlibNt.Wu2008DoubleSieve.HighSixU3Splice

namespace Wu2008DoubleSieve.HighSixTail
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open SingleUpperCounts SingleUpperSplice SingleUpperNormalization
open SingleUpperQuadrature SingleUpperPrimePayment SingleUpperHighQuadrature
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

noncomputable def tailPrimes (N : ℕ) : Finset ℕ :=
  primeWindow N ((N : ℝ)^HighSix.right) ((N : ℝ)^(1/3 : ℝ))

/-- Tail inclusion is used only for pointwise geometry and positive main terms. -/
theorem tail_high {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N) (hδ : 0 ≤ δ)
    (hp : p ∈ tailPrimes N) : p ∈ highPrimes N δ (1/3) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨hpp,hcop,hl,hr⟩ := mem_primeWindow.mp hp
  apply mem_filter.mpr
  constructor
  · exact mem_primeWindow.mpr ⟨hpp,hcop,
      (rpow_le_rpow_of_exponent_le hn (by norm_num [truncatedSixthLowerAlpha,HighSix.right])).trans hl,hr⟩
  · exact (rpow_le_rpow_of_exponent_le hn (by norm_num [HighSix.right]; linarith)).trans hl

noncomputable def tailDensityMass (N : ℕ) (δ ρ : ℝ) : ℝ :=
  ∑ p ∈ tailPrimes N,
    (logarithmicIntegral N / (Nat.totient p : ℝ)) *
      ((jr1965F (((1/2-δ)-log (p : ℝ)/log (N : ℝ))/truncatedSixthLowerAlpha)+ρ) *
        localSieveProduct N ((N : ℝ)^truncatedSixthLowerAlpha))

/-- Rosser is instantiated on the actual right mask, with its signed remainder intact. -/
theorem tail_finite_upper {N : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100) :
    HighSix.U3tailCount N ≤
    (∑ p ∈ tailPrimes N,
      (logarithmicIntegral N / (Nat.totient p : ℝ)) *
        ordinaryRosserMainSum true N p (wuVariableRosserLevel N δ p)
          ((N : ℝ)^truncatedSixthLowerAlpha)) +
    ∑ p ∈ tailPrimes N,
      ordinaryRosserRemainder true N p (wuVariableRosserLevel N δ p)
        ((N : ℝ)^truncatedSixthLowerAlpha) := by
  have ha : HighSix.alpha = truncatedSixthLowerAlpha := by
    norm_num [HighSix.alpha,truncatedSixthLowerAlpha]
  unfold HighSix.U3tailCount
  rw [ha, ← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  have hpw := (mem_filter.mp (tail_high hN hδ hp)).1
  have hg := full_level_geometry hN hδhi (le_refl (1/3 : ℝ)) hpw
  rw [← source_count (mem_primeWindow.mp hpw).1 (mem_primeWindow.mp hpw).2.2.1]
  exact ordinaryRosser_upper_finite hg.1 hg.2.2

/-- Global signed BV is called anew on the tail; no signed-subset monotonicity. -/
theorem actual_tail_density {δ ρ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      HighSix.U3tailCount N ≤ tailDensityMass N δ ρ + ε * truncatedSixthMassScale N := by
  obtain ⟨TB,hTB4,hBV⟩ := masked_remainder_small hδ hε
  obtain ⟨TD,_,hD⟩ := high_prime_density hδ.le hδhi hρ
  refine ⟨max TB TD,hTB4.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hNB : TB ≤ N := (le_max_left _ _).trans hN
  have hND : TD ≤ N := (le_max_right _ _).trans hN
  have hN4 := hTB4.trans hNB
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  have hmain : (∑ p ∈ tailPrimes N,
      (logarithmicIntegral N / (Nat.totient p : ℝ)) *
        ordinaryRosserMainSum true N p (wuVariableRosserLevel N δ p)
          ((N : ℝ)^truncatedSixthLowerAlpha)) ≤ tailDensityMass N δ ρ := by
    apply sum_le_sum
    intro p hp
    have hh := mem_filter.mp (tail_high (by omega) hδ.le hp)
    exact mul_le_mul_of_nonneg_left (hD N hND he (1/3) le_rfl p hh.1 hh.2)
      (div_nonneg hli (Nat.cast_nonneg _))
  have hrem := hBV N hNB (tailPrimes N) (fun p hp => by
    have hw := mem_primeWindow.mp (mem_filter.mp (tail_high (by omega) hδ.le hp)).1
    exact ⟨hw.1,hw.2.1,hw.2.2.1⟩)
  have hf := tail_finite_upper (δ := δ) (by omega : 2 ≤ N) hδ.le hδhi
  linarith [le_abs_self (∑ p ∈ tailPrimes N,
    ordinaryRosserRemainder true N p (wuVariableRosserLevel N δ p)
      ((N : ℝ)^truncatedSixthLowerAlpha))]

end Wu2008DoubleSieve.HighSixTail
