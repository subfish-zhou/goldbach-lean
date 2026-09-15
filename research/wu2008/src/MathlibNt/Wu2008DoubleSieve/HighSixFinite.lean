import MathlibNt.Wu2008DoubleSieve.HighSixGeometry

namespace Wu2008DoubleSieve.HighSix
open Finset Real
open scoped Classical
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def O1 (N : ℕ) (δ : ℝ) : ℝ := ∑ p ∈ P N, wuOmega1 N p δ S
noncomputable def O2 (N : ℕ) (δ : ℝ) : ℝ := ∑ p ∈ P N, wuOmega2 N p δ s S
noncomputable def O3 (N : ℕ) (δ : ℝ) : ℝ := ∑ p ∈ P N, wuOmega3 N p δ s S
noncomputable def C6 (N : ℕ) : ℝ := ∑ p ∈ P N, (sieveCount N p N ((N : ℝ)^alpha) : ℝ)
noncomputable def B6 (N : ℕ) (δ : ℝ) : ℝ :=
  boxTheta N ((N : ℝ)^(1/2-δ)) (fun _ : Fin 1 => P N)
noncomputable def J : ℝ := ∫ v in (1-1/s)..(1-1/S), log (S*v-1)/(v*(1-v))
noncomputable def pairMain (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ P N, ∑ q ∈ primeWindow N (z N δ p) (w N δ p),
    (logarithmicIntegral N / (Nat.totient (p*q) : ℝ)) *
      ordinaryRosserMainSum false N (p*q) (wuVariableRosserLevel N δ (p*q)) (z N δ p)
noncomputable def pairRemainder (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ P N, ∑ q ∈ primeWindow N (z N δ p) (w N δ p),
    ordinaryRosserRemainder false N (p*q) (wuVariableRosserLevel N δ (p*q)) (z N δ p)

/-- The actual first mother inequality, with no repeated lane or source box. -/
theorem count_finite {N : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    2*C6 N ≤ O1 N δ - O2 N δ + O3 N δ := by
  have hpoint (p : ℕ) (hp : p ∈ P N) :
      2*(sieveCount N p N ((N : ℝ)^alpha) : ℝ) ≤
        wuOmega1 N p δ S - wuOmega2 N p δ s S + wuOmega3 N p δ s S := by
    have hg := cutoff_geometry hN hδ hδhi hp
    have hf := wu_omega_weighted_finite N p hg.2.1
    rw [repeated_zero hN hδ hδhi hp, add_zero] at hf
    have hm : (sourceSieveCount N p (p*N) ((N : ℝ)^alpha) : ℝ) ≤
        (sourceSieveCount N p (p*N) (w N δ p) : ℝ) := by
      exact_mod_cast sourceSieveCount_antitone N p (p*N) hg.2.2.1
    rw [SingleUpperCounts.source_count (mem_primeWindow.mp hp).1 hg.2.2.2.le] at hm
    exact (mul_le_mul_of_nonneg_left hm (by norm_num)).trans hf
  have hf := sum_le_sum hpoint
  simpa only [C6, O1, O2, O3, sum_add_distrib, sum_sub_distrib, ← mul_sum] using hf

/-- Full cofactor, selected modulus and label-dependent cutoff are retained. -/
theorem omega2_finite_lower {N : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    pairMain N δ + pairRemainder N δ ≤ O2 N δ := by
  unfold pairMain pairRemainder O2 wuOmega2
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro q hq
  have hg := pair_level_geometry hN hδ hδhi hp hq
  rw [source_pair_count (N := N) (p := p) (v := wuLocalCutoff N δ p S)
    (mem_primeWindow.mp hq).1 (mem_primeWindow.mp hq).2.2.1]
  exact ordinaryRosser_lower_finite hg.2

end Wu2008DoubleSieve.HighSix
