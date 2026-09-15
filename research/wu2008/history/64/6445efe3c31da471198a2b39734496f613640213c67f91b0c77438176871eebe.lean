import MathlibNt.Wu2008DoubleSieve.ConvolutionMultiplicity
import MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Ordinary Bombieri--Vinogradov for actual prime-window convolutions

This supplies the ordinary prime-AP remainder used in Wu (2004), (3.13).
The analytic input is the frozen unconditional Richert (4.18) theorem.
It is not the switching remainder, a double-sieve comparison, or a density
asymptotic.
-/

namespace Wu2008DoubleSieve

open Finset Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The literal nonnegative ordinary-AP remainder. The outer truncation loses
no positive-`q` terms: `d > Q` implies `Q / d = 0`. -/
noncomputable def convolutionAPError {k : ℕ} (N Q : ℕ)
    (W : Fin k → Finset ℕ) : ℝ :=
  ∑ d ∈ Icc 1 Q, (convolutionCoeff W d : ℝ) *
    ∑ q ∈ (Icc 1 (Q / d)).filter (fun q => q.Coprime (d * N)),
      |primeAPError N (d * q) N|

/-- The finite outer truncation is exactly the sum over the full literal
convolution support, not an estimate discarding any contribution. -/
theorem convolutionAPError_eq_support_sum {k : ℕ} (N Q : ℕ)
    (W : Fin k → Finset ℕ) :
    convolutionAPError N Q W =
      ∑ d ∈ (Fintype.piFinset W).image (fun t => ∏ j, t j),
        (convolutionCoeff W d : ℝ) *
          ∑ q ∈ (Icc 1 (Q / d)).filter (fun q => q.Coprime (d * N)),
            |primeAPError N (d * q) N| := by
  let S := (Fintype.piFinset W).image (fun t => ∏ j, t j)
  let r := fun d => (convolutionCoeff W d : ℝ) *
    ∑ q ∈ (Icc 1 (Q / d)).filter (fun q => q.Coprime (d * N)),
      |primeAPError N (d * q) N|
  change ∑ d ∈ Icc 1 Q, r d = ∑ d ∈ S, r d
  calc
    _ = ∑ d ∈ Icc 1 Q ∪ S, r d := by
      apply sum_subset subset_union_left
      intro d _ hd
      by_cases hd0 : d = 0
      · simp [r, hd0]
      have hQd : Q < d := by
        simp only [mem_Icc] at hd
        omega
      simp [r, Nat.div_eq_of_lt hQd]
    _ = ∑ d ∈ S, r d := by
      symm
      apply sum_subset subset_union_right
      intro d _ hd
      have hzero : convolutionCoeff W d = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hpos
        obtain ⟨t, ht, hprod⟩ := convolutionCoeff_pos_iff.mp hpos
        exact hd (mem_image.mpr ⟨t, Fintype.mem_piFinset.mpr ht, hprod⟩)
      simp [r, hzero]

theorem primeAPError_mod_residue (N m : ℕ) :
    primeAPError N m N = primeAPError N m (N % m) := by
  unfold primeAPError MathlibNt.SieveTheory.BombieriVinogradov.primesInAP
  simp only [Nat.ModEq, Nat.mod_mod]
  rfl

theorem abs_primeAPError_le_prefix (N m : ℕ) (hN : 2 ≤ N)
    (hm : 0 < m) (hcop : N.Coprime m) :
    |primeAPError N m N| ≤ primeAPPrefixMaxError N m := by
  rw [primeAPError_mod_residue]
  apply (abs_primeAPError_le_residueMax ?_).trans
    (primeAPResidueMaxError_le_prefixMax (mem_Icc.mpr ⟨hN, le_rfl⟩))
  simp only [AnalyticNumberTheory.Sieve.unitResidues, mem_filter, mem_range]
  exact ⟨Nat.mod_lt N hm, (ZMod.coprime_mod_iff_coprime N m).mpr hcop⟩

/-- Exact positive-modulus reindexing `m = d*q`. -/
theorem sum_multiples_eq (Q d : ℕ) (hd : 0 < d) (E : ℕ → ℝ) :
    (∑ q ∈ Icc 1 (Q / d), E (d * q)) =
      ∑ m ∈ (Icc 1 Q).filter (fun m => d ∣ m), E m := by
  apply sum_bij (fun q _ => d * q)
  · intro q hq
    obtain ⟨hq1, hqQ⟩ := mem_Icc.mp hq
    exact mem_filter.mpr ⟨mem_Icc.mpr
      ⟨Nat.mul_pos hd hq1, by
        have := (Nat.le_div_iff_mul_le hd).mp hqQ
        simpa [Nat.mul_comm] using this⟩, dvd_mul_right d q⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hd hab
  · intro m hm
    obtain ⟨hm, hdm⟩ := mem_filter.mp hm
    refine ⟨m / d, mem_Icc.mpr ⟨?_, Nat.div_le_div_right (mem_Icc.mp hm).2⟩,
      Nat.mul_div_cancel' hdm⟩
    exact Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hm).1 hdm) hd
  · intro _ _
    rfl

private theorem divisor_filter_eq {Q m : ℕ} (hm : m ∈ Icc 1 Q) :
    (Icc 1 Q).filter (fun d => d ∣ m) = m.divisors := by
  ext d
  simp only [mem_filter, mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨_, hdm⟩
    exact ⟨hdm, Nat.ne_of_gt (mem_Icc.mp hm).1⟩
  · rintro ⟨hdm, hmn⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdm (Nat.pos_of_ne_zero hmn),
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hmn) hdm).trans (mem_Icc.mp hm).2⟩, hdm⟩

/-- Finite regrouping, with the complete divisor multiplicity left visible. -/
theorem convolutionAPError_le_divisor_sum {k N Q : ℕ}
    (W : Fin k → Finset ℕ) (hN : 2 ≤ N)
    (hW : ∀ j p, p ∈ W j → p.Coprime N) :
    convolutionAPError N Q W ≤
      ∑ m ∈ Icc 1 Q,
        ((∑ d ∈ m.divisors, convolutionCoeff W d : ℕ) : ℝ) *
          primeAPPrefixMaxError N m := by
  let E := primeAPPrefixMaxError N
  have hmajor :
      convolutionAPError N Q W ≤
        ∑ d ∈ Icc 1 Q, (convolutionCoeff W d : ℝ) *
          ∑ m ∈ (Icc 1 Q).filter (fun m => d ∣ m), E m := by
    apply sum_le_sum
    intro d hd
    by_cases hσ : convolutionCoeff W d = 0
    · simp [hσ]
    have hdN := convolutionCoeff_coprime hW (Nat.pos_of_ne_zero hσ)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [← sum_multiples_eq Q d (mem_Icc.mp hd).1 E]
    calc
      _ ≤ ∑ q ∈ (Icc 1 (Q / d)).filter (fun q => q.Coprime (d * N)),
          E (d * q) := by
        apply sum_le_sum
        intro q hq
        obtain ⟨hq, hcop⟩ := mem_filter.mp hq
        apply abs_primeAPError_le_prefix N (d * q) hN
          (Nat.mul_pos (mem_Icc.mp hd).1 (mem_Icc.mp hq).1)
        exact hdN.symm.mul_right (hcop.of_dvd_right (dvd_mul_left N d)).symm
      _ ≤ ∑ q ∈ Icc 1 (Q / d), E (d * q) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun q _ _ => primeAPPrefixMaxError_nonneg N (d * q))
  refine hmajor.trans_eq ?_
  simp_rw [sum_filter, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  rw [← sum_filter]
  rw [divisor_filter_eq hm, ← sum_mul, Nat.cast_sum]

/-- A pointwise bound with a constant independent of all prime windows. -/
theorem convolutionAPError_le_maximal_sum {i k N Q : ℕ} {α : ℝ}
    (W : Fin i → Finset ℕ) (hik : i ≤ k)
    (hN : 2 ≤ N) (hQN : Q ≤ N) (hα : 0 < α)
    (hW : ∀ j p, p ∈ W j →
      p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ α ≤ (p : ℝ)) :
    convolutionAPError N Q W ≤
      (max 1 (1 / α)) ^ k * ∑ m ∈ Icc 1 Q, primeAPPrefixMaxError N m := by
  apply (convolutionAPError_le_divisor_sum W hN (fun j p hp => (hW j p hp).2.1)).trans
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_right _ (primeAPPrefixMaxError_nonneg N m)
  exact convolutionCoeff_divisor_mass_le_depth W hik (by omega)
    (mem_Icc.mp hm).1 ((mem_Icc.mp hm).2.trans hQN) hα
    (fun j p hp => ⟨(hW j p hp).1, (hW j p hp).2.2⟩)

/-- The integer moduli in the real range `m ≤ N^(1/2-δ)`. -/
noncomputable def convolutionModulusCutoff (N : ℕ) (δ : ℝ) : ℕ :=
  ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊

/-- Floors encode the exact real combined-modulus restriction. -/
theorem convolutionModulusCutoff_quotient_iff {N d q : ℕ} (δ : ℝ) (hd : 0 < d) :
    q ≤ convolutionModulusCutoff N δ / d ↔
      (d : ℝ) * (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) := by
  rw [Nat.le_div_iff_mul_le hd]
  unfold convolutionModulusCutoff
  rw [Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  simp only [Nat.cast_mul, mul_comm]

theorem eventually_log_rpow_le_rpow (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ B ≤ (N : ℝ) ^ δ := by
  have hbound := (isLittleO_log_rpow_rpow_atTop B hδ).bound (show (0 : ℝ) < 1 by norm_num)
  have hreal : ∀ᶠ x : ℝ in atTop, Real.log x ^ B ≤ x ^ δ := by
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) B),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) δ), one_mul] using hx
  exact tendsto_natCast_atTop_atTop.eventually hreal

theorem convolutionModulusCutoff_le_self {N : ℕ} {δ : ℝ}
    (hN : 1 ≤ N) (hδ : 0 < δ) : convolutionModulusCutoff N δ ≤ N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (1 / 2 - δ) ≤ (N : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN' (by linarith)
      _ = _ := Real.rpow_one _
  exact_mod_cast (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)).trans hpow

theorem convolutionModulusCutoff_eventually_le_pan (B : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, convolutionModulusCutoff N δ ≤
      MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B := by
  filter_upwards [eventually_log_rpow_le_rpow B hδ,
    eventually_ge_atTop (2 : ℕ)] with N hlog hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  unfold convolutionModulusCutoff MathlibNt.SieveTheory.LiuWeight.panModulusCutoff
  apply Nat.floor_mono
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hl B)).mpr
  calc
    (N : ℝ) ^ (1 / 2 - δ) * Real.log (N : ℝ) ^ B ≤
        (N : ℝ) ^ (1 / 2 - δ) * (N : ℝ) ^ δ :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring

/-- Unconditional ordinary-AP BV for literal convolutions of at most `k`
arbitrary finite prime windows above `N^α`. Both constants precede `N`, the
depth, and every window. Evenness and upper-window bounds are unnecessary. -/
theorem convolution_bombieri_vinogradov (k : ℕ) {α δ A : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ i : ℕ, i ≤ k → ∀ W : Fin i → Finset ℕ,
        (∀ j p, p ∈ W j →
          p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ α ≤ (p : ℝ)) →
        convolutionAPError N (convolutionModulusCutoff N δ) W ≤
          C * (N : ℝ) / Real.log N ^ A := by
  obtain ⟨B, _, K, hK, hBV⟩ := richert418 A hA
  let M : ℝ := (max 1 (1 / α)) ^ k
  have hM : 0 < M := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨M * K, mul_pos hM hK, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hBV, convolutionModulusCutoff_eventually_le_pan B hδ,
    eventually_ge_atTop (2 : ℕ)] with N hBVN hcut hN
  intro i hik W hW
  calc
    convolutionAPError N (convolutionModulusCutoff N δ) W ≤
        M * ∑ m ∈ Icc 1 (convolutionModulusCutoff N δ), primeAPPrefixMaxError N m :=
      convolutionAPError_le_maximal_sum W hik hN
        (convolutionModulusCutoff_le_self (by omega) hδ) hα hW
    _ ≤ M * ∑ m ∈ Icc 1 (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B),
        primeAPPrefixMaxError N m := by
      apply mul_le_mul_of_nonneg_left _ hM.le
      exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hcut)
        (fun m _ _ => primeAPPrefixMaxError_nonneg N m)
    _ ≤ M * (K * (N : ℝ) / Real.log N ^ A) :=
      mul_le_mul_of_nonneg_left (hBVN hN) hM.le
    _ = (M * K) * (N : ℝ) / Real.log N ^ A := by ring

end Wu2008DoubleSieve
