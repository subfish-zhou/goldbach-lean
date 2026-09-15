import MathlibNt.Wu2008DoubleSieve.BaseLowerAssembly
import MathlibNt.Wu2008DoubleSieve.CanonicalUpperExtension
import MathlibNt.Wu2008DoubleSieve.VariableLevelGeometry

namespace Wu2008DoubleSieve.SingleUpperCounts
open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The selected prime is not a small sieve prime, including at the strict endpoint. -/
theorem sifted_selected_modulus {N p n : ℕ} {z : ℝ}
    (hp : p.Prime) (hz : z ≤ (p : ℝ)) :
    Sifted (p * N) n z ↔ Sifted N n z := by
  constructor
  · intro h q hq hc hqz
    apply h q hq (Nat.coprime_mul_iff_right.mpr ⟨?_, hc⟩) hqz
    exact (Nat.coprime_primes hq hp).mpr (by
      intro he
      subst q
      exact (not_lt_of_ge hz) hqz)
  · intro h q hq hc hqz
    exact h q hq (Nat.coprime_mul_iff_right.mp hc).2 hqz

/-- Exact carrier equality retains the unit quotient and all prime remainders. -/
theorem source_carrier {N p : ℕ} {z : ℝ} (hp : p.Prime) (hz : z ≤ (p : ℝ)) :
    sourceSieveCarrier N p (p * N) z = sieveCarrier N p N z := by
  rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right p N)]
  ext q
  simp only [sieveCarrier, mem_filter, sifted_selected_modulus hp hz]

theorem source_count {N p : ℕ} {z : ℝ} (hp : p.Prime) (hz : z ≤ (p : ℝ)) :
    sourceSieveCount N p (p * N) z = sieveCount N p N z := by
  unfold sourceSieveCount sieveCount
  rw [source_carrier hp hz]

/-- A one-coordinate convolution is the literal indicator, not a set of products
with a lost tuple multiplicity. -/
theorem single_coeff (P : Finset ℕ) (d : ℕ) :
    convolutionCoeff (fun _ : Fin 1 => P) d = if d ∈ P then 1 else 0 := by
  have he : (Fintype.piFinset (fun _ : Fin 1 => P)).filter
      (fun t => ∏ j, t j = d) = if d ∈ P then {fun _ : Fin 1 => d} else ∅ := by
    ext t
    simp only [mem_filter, Fintype.mem_piFinset, Fin.prod_univ_one]
    by_cases hd : d ∈ P
    · simp only [if_pos hd, mem_singleton]
      constructor
      · intro ht
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        simpa only [hj] using ht.2
      · rintro rfl
        exact ⟨fun _ => hd, rfl⟩
    · simp only [if_neg hd, notMem_empty, iff_false, not_and]
      intro ht heq
      exact hd (heq ▸ ht 0)
  simp only [convolutionCoeff, he]
  split <;> simp

theorem single_support (P : Finset ℕ) :
    (Fintype.piFinset (fun _ : Fin 1 => P)).image (fun t => ∏ j, t j) = P := by
  ext d
  constructor
  · rintro hd
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hd
    simpa only [Fin.prod_univ_one] using Fintype.mem_piFinset.mp ht 0
  · intro hd
    exact mem_image.mpr ⟨fun _ => d, Fintype.mem_piFinset.mpr (fun _ => hd), by simp⟩

theorem single_weighted_sum (P : Finset ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin 1 => P)).image (fun t => ∏ j, t j),
      (convolutionCoeff (fun _ : Fin 1 => P) d : ℝ) * f d) = ∑ p ∈ P, f p := by
  rw [single_support]
  apply sum_congr rfl
  intro d hd
  simp only [single_coeff, if_pos hd, Nat.cast_one, one_mul]

/-- Full original single-prime count, with weight one. -/
noncomputable def U (N : ℕ) (r : ℝ) : ℤ :=
  ∑ p ∈ primeWindow N ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^r),
    sieveCount N p N ((N : ℝ)^truncatedSixthLowerAlpha)

noncomputable def main (N : ℕ) (δ r : ℝ) : ℝ :=
  ∑ p ∈ primeWindow N ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^r),
    (logarithmicIntegral N / (Nat.totient p : ℝ)) *
      ordinaryRosserMainSum true N p (wuVariableRosserLevel N δ p)
        ((N : ℝ)^truncatedSixthLowerAlpha)

noncomputable def remainder (N : ℕ) (δ r : ℝ) : ℝ :=
  ∑ p ∈ primeWindow N ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^r),
    ordinaryRosserRemainder true N p (wuVariableRosserLevel N δ p)
      ((N : ℝ)^truncatedSixthLowerAlpha)

/-- Every prime through N^(1/3) has the full z^2 level margin; no squared-prefix
condition is present. This is symbolic rational geometry only. -/
theorem full_level_geometry {N p : ℕ} {δ r : ℝ}
    (hN : 2 ≤ N) (hδ : δ ≤ 1/100) (hr : r ≤ 1/3)
    (hp : p ∈ primeWindow N ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^r)) :
    1 < wuVariableRosserLevel N δ p ∧
      ((N : ℝ)^truncatedSixthLowerAlpha)^2 ≤ (N : ℝ)^(1/2-δ)/(p : ℝ) ∧
      (N : ℝ)^truncatedSixthLowerAlpha ≤ (wuVariableRosserLevel N δ p : ℝ) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primeWindow.mp hp).1.pos
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have hz1 : 1 < (N : ℝ)^truncatedSixthLowerAlpha := one_lt_rpow hN1 ha
  have hpup := (mem_primeWindow.mp hp).2.2.2.le
  have he : 2*truncatedSixthLowerAlpha + r ≤ (1/2 : ℝ)-δ := by
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hzz : ((N : ℝ)^truncatedSixthLowerAlpha)^2 ≤ (N : ℝ)^(1/2-δ)/(p : ℝ) := by
    apply (le_div_iff₀ hp0).mpr
    calc
      _ ≤ ((N : ℝ)^truncatedSixthLowerAlpha)^2 * (N : ℝ)^r :=
        mul_le_mul_of_nonneg_left hpup (by positivity)
      _ = (N : ℝ)^(2*truncatedSixthLowerAlpha+r) := by
        rw [pow_two, ← rpow_add hN0, ← rpow_add hN0]
        congr 1
        ring
      _ ≤ _ := rpow_le_rpow_of_exponent_le hN1.le he
  have hzq : (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^(1/2-δ)/(p : ℝ) :=
    (show (N : ℝ)^truncatedSixthLowerAlpha ≤ ((N : ℝ)^truncatedSixthLowerAlpha)^2 by nlinarith).trans hzz
  have hfloor : (N : ℝ)^(1/2-δ)/(p : ℝ) < (wuVariableRosserLevel N δ p : ℝ) := by
    unfold wuVariableRosserLevel
    exact_mod_cast Nat.lt_floor_add_one ((N : ℝ)^(1/2-δ)/(p : ℝ))
  refine ⟨?_, hzz, hzq.trans hfloor.le⟩
  exact_mod_cast hz1.trans (hzq.trans_lt hfloor)

/-- Actual finite upper bound over the whole window, with the signed aggregate
left intact. No analytic count or AP hypothesis is supplied. -/
theorem actual_finite_upper {N : ℕ} {δ r : ℝ}
    (hN : 2 ≤ N) (hδ : δ ≤ 1/100) (hr : r ≤ 1/3) :
    (U N r : ℝ) ≤ main N δ r + remainder N δ r := by
  unfold U main remainder
  rw [Int.cast_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  have hg := full_level_geometry hN hδ hr hp
  rw [← source_count (mem_primeWindow.mp hp).1 (mem_primeWindow.mp hp).2.2.1]
  exact ordinaryRosser_upper_finite hg.1 hg.2.2

/-- Global BV payment on arbitrary moving upper endpoints and arbitrary masks.
The sole triangle step is backed by the frozen bounded-divisor-multiplicity
regrouping; the threshold precedes P, signs, cutoffs and natural levels. -/
theorem global_signed_bv {α δ A : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      ∀ P : Finset ℕ,
        (∀ p ∈ P, p.Prime ∧ p.Coprime N ∧ (N : ℝ)^α ≤ (p : ℝ)) →
      ∀ upper : Bool, ∀ D : ℕ → ℕ, ∀ z : ℕ → ℝ,
        (∀ p ∈ P, D p ≤ convolutionModulusCutoff N δ / p + 1) →
        |∑ p ∈ P, ordinaryRosserRemainder upper N p (D p) (z p)| ≤
          C * N / log (N : ℝ)^A := by
  obtain ⟨C, hC, T, hBV⟩ := convolution_bombieri_vinogradov 1 hα hδ hA
  refine ⟨C, hC, T, ?_⟩
  intro N hN P hP upper D z hD
  have hb := hBV N hN 1 le_rfl (fun _ => P) (fun _ p hp => hP p hp)
  have hs := convolutionRosserRemainder_le_AP (N := N) (Q := convolutionModulusCutoff N δ)
    (fun _ : Fin 1 => P) upper D z (by simpa only [single_support] using hD)
  rw [convolutionRosserRemainder, single_weighted_sum] at hs
  exact hs.trans hb

/-- One epsilon budget pays the whole signed prime aggregate. The threshold is
uniform in every upper endpoint, including both original overlapping windows. -/
theorem remainder_small {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ r : ℝ,
      |remainder N δ r| ≤ ε * truncatedSixthMassScale N := by
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  obtain ⟨C, hC, T, hBV⟩ := global_signed_bv ha hδ (show (0 : ℝ) < 3 by norm_num)
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  have ht : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (C/(ε*wuSingularSeries 1))))
  refine ⟨max 4 (max T M), le_max_left _ _, ?_⟩
  intro N hN r
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNT : T ≤ N := (le_max_left T M).trans ((le_max_right _ _).trans hN)
  have hNM : M ≤ N := (le_max_right T M).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hseries : wuSingularSeries 1 ≤ wuSingularSeries N :=
    wuSingularSeries_le_of_dvd (by norm_num) (by omega) (one_dvd N)
  have hbudget : C / log (N : ℝ) ≤ ε * wuSingularSeries N := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hC1)).mp (hM N hNM)
    have hs := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hseries hε.le) hlog.le
    nlinarith
  have hb := hBV N hNT
    (primeWindow N ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^r))
    (fun p hp => ⟨(mem_primeWindow.mp hp).1, (mem_primeWindow.mp hp).2.1,
      (mem_primeWindow.mp hp).2.2.1⟩)
    true (wuVariableRosserLevel N δ) (fun _ => (N : ℝ)^truncatedSixthLowerAlpha)
    (fun p _ => (wuVariableRosserLevel_eq_combined N p δ).le)
  change |remainder N δ r| ≤ C * N / log (N : ℝ)^(3 : ℝ) at hb
  have hb' : |remainder N δ r| ≤ C * N / log (N : ℝ)^(3 : ℕ) := by
    convert hb using 1
    norm_num
  calc
    _ ≤ C * N / log (N : ℝ)^(3 : ℕ) := hb'
    _ = (C / log (N : ℝ)) * ((N : ℝ)/log (N : ℝ)^(2 : ℕ)) := by ring
    _ ≤ (ε * wuSingularSeries N) * ((N : ℝ)/log (N : ℝ)^(2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = _ := by unfold truncatedSixthMassScale; ring

/-- Complete actual prime window, after unconditional aggregate BV payment.
This is a Rosser-main bound, not yet the classical integral asymptotic. -/
theorem actual_upper_main {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ r : ℝ, r ≤ 1/3 →
      (U N r : ℝ) ≤ main N δ r + ε * truncatedSixthMassScale N := by
  obtain ⟨T, hT4, hT⟩ := remainder_small hδ hε
  refine ⟨T, hT4, ?_⟩
  intro N hN r hr
  have hf : (U N r : ℝ) ≤ main N δ r + remainder N δ r :=
    actual_finite_upper (N := N) (δ := δ) (r := r) (by omega) hδhi hr
  have hb : remainder N δ r ≤ ε * truncatedSixthMassScale N :=
    (le_abs_self (remainder N δ r)).trans (hT N hN r)
  exact hf.trans (add_le_add le_rfl hb)

/-- Both original negative summands with one common threshold and one shared
error. Their overlap is added twice, never replaced by a union. -/
theorem both_upper_main {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      (U N (1/3) : ℝ) + (U N truncatedSixthLowerSigma : ℝ) ≤
        main N δ (1/3) + main N δ truncatedSixthLowerSigma +
          ε * truncatedSixthMassScale N := by
  obtain ⟨T, hT4, hT⟩ := actual_upper_main hδ hδhi (half_pos hε)
  refine ⟨T, hT4, ?_⟩
  intro N hN
  have hσ : truncatedSixthLowerSigma ≤ (1/3 : ℝ) := by
    norm_num [truncatedSixthLowerSigma, truncatedSixthLowerAlpha]
  have h1 := hT N hN (1/3) le_rfl
  have h2 := hT N hN truncatedSixthLowerSigma hσ
  linarith

end Wu2008DoubleSieve.SingleUpperCounts
