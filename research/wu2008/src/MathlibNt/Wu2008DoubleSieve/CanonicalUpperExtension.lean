import MathlibNt.Wu2008DoubleSieve.CanonicalLowerDensity
import MathlibNt.Wu2008DoubleSieve.PhiMonotone
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965ChenDelayMonotonicity

/-!
# Canonical upper density beyond the initial branch

The constructed JR upper function equals the explicit integral factor through
five. The existing actual Rosser density producer, however, reaches only four;
we do not extend its analytic range by extending the factor identity.
All density products use the strict prime cutoff.
The actual Phi aggregate is bounded on `[1,4]` with coefficient
`s*jr1965F(s)/(2*exp(gamma))`; its closed version follows by finite
monotonicity, not by identifying strict and closed carriers.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- Integrating the constructed first lower branch identifies the next upper
branch. The factor identity extends through five, not the density theorem. -/
theorem jr1965F_eq_innerIntegral {s : ℝ} (hs3 : 3 ≤ s) (hs5 : s ≤ 5) :
    jr1965F s = 2 * exp eulerMascheroniConstant / s *
      (1 + jurkatRichertInnerIntegral s) := by
  have hrec := jr1965F_integral_recurrence (v := 3) (by norm_num) hs3
  have hint :
      (∫ t in (3 : ℝ)..s, jr1965f (t - 1)) =
        (2 * exp eulerMascheroniConstant) * jurkatRichertInnerIntegral s := by
    calc
      _ = ∫ t in (3 : ℝ)..s,
          (2 * exp eulerMascheroniConstant) *
            (log ((t - 1) - 1) / (t - 1)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hs3] at ht
        change jr1965f (t - 1) =
          (2 * exp eulerMascheroniConstant) * (log ((t - 1) - 1) / (t - 1))
        rw [jr1965f_eq_log_firstInterval (by linarith [ht.1]) (by linarith [ht.2])]
        ring
      _ = (2 * exp eulerMascheroniConstant) *
          ∫ t in (3 : ℝ)..s, log ((t - 1) - 1) / (t - 1) :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_right
          (fun t : ℝ => log (t - 1) / t) 1]
        norm_num [jurkatRichertInnerIntegral]
  rw [jr1965F_eq_of_le_three (u := 3) (by norm_num), hint] at hrec
  have hsne : s ≠ 0 := by linarith
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hsne).2
  field_simp at hrec ⊢
  nlinarith

/-- Exact identification with the frozen explicit upper factor. Its initial
branch includes the real zero convention of the constructed function. -/
theorem jr1965F_eq_upperLinearSieveFactor {s : ℝ} (hs5 : s ≤ 5) :
    jr1965F s = jurkatRichertUpperLinearSieveFactor s := by
  by_cases hs3 : s ≤ 3
  · simp only [jr1965F_eq_of_le_three hs3, jurkatRichertUpperLinearSieveFactor,
      if_pos hs3]
  · simpa only [jurkatRichertUpperLinearSieveFactor, if_neg hs3] using
      jr1965F_eq_innerIntegral (lt_of_not_ge hs3).le hs5

/-- Actual canonical upper density on `[3/2,4]`. Its threshold is chosen
before every modulus and every real cutoff, level and source parameter. -/
theorem ordinaryRosser_upper_density_canonical_extended {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N d : ℕ, ∀ _he : Even N, ∀ z level s : ℝ,
      z0 ≤ z → 2 ≤ z → 0 < level →
      s = log level / log z → 3 / 2 ≤ s → s ≤ 4 →
      ordinaryRosserMainSum true N d (⌊level⌋₊ + 1) z ≤
        (jr1965F s + ρ) *
          ∏ p ∈ primeWindow (d * N) 0 z, (1 - 1 / ((p : ℝ) - 1)) := by
  obtain ⟨z0, hbound⟩ := ordinaryRosser_upper_density_uniform hρ
  refine ⟨z0, ?_⟩
  intro N d he z level s hz0 hz hlevel hs hslo hshi
  simpa only [jr1965F_eq_upperLinearSieveFactor (show s ≤ 5 by linarith)] using
    hbound N d he z level s hz0 hz hlevel hs hslo hshi

/-- The extended canonical density in the exact actual local-product
normalization; no asymptotic replacement is made in this identity. -/
theorem ordinaryRosser_upper_density_canonical_extended_local {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N d : ℕ, ∀ _he : Even N, ∀ z level s : ℝ,
      z0 ≤ z → 2 ≤ z → 0 < level →
      s = log level / log z → 3 / 2 ≤ s → s ≤ 4 →
      ordinaryRosserMainSum true N d (⌊level⌋₊ + 1) z ≤
        (jr1965F s + ρ) * localSieveProduct (d * N) z := by
  obtain ⟨z0, hbound⟩ := ordinaryRosser_upper_density_canonical_extended hρ
  refine ⟨z0, ?_⟩
  intro N d he z level s hz0 hz hlevel hs hslo hshi
  simpa only [localSieveProduct, localSievePrimes_eq_primeWindow] using
    hbound N d he z level s hz0 hz hlevel hs hslo hshi

/-- Wu's actual upper coefficient on the initial branch. -/
theorem jr1965F_normalized_initial {s : ℝ} (hs : 0 < s) (hs3 : s ≤ 3) :
    s * jr1965F s / (2 * exp eulerMascheroniConstant) = 1 := by
  rw [jr1965F_eq_of_le_three hs3]
  have hsne : s ≠ 0 := hs.ne'
  field_simp

/-- The next coefficient is the explicit inner integral, not the base
constant one. Its formula is valid through five. -/
theorem jr1965F_normalized_innerIntegral {s : ℝ} (hs3 : 3 ≤ s) (hs5 : s ≤ 5) :
    s * jr1965F s / (2 * exp eulerMascheroniConstant) =
      1 + jurkatRichertInnerIntegral s := by
  rw [jr1965F_eq_innerIntegral hs3 hs5]
  have hsne : s ≠ 0 := by linarith
  field_simp

/-- Uniform budget on `[1,4]`. The frozen global monotonicity bound
`F(s)<=2*exp(gamma)` gives `A(s)<=4`; the actual coefficient is retained. -/
theorem canonical_upper_extended_normalization_budget {s C l η : ℝ}
    (hs1 : 1 ≤ s) (hs4 : s ≤ 4) (hC : 0 ≤ C) (hl : 0 < l)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    (jr1965F s + exp eulerMascheroniConstant * η / 2) *
        ((1 + η) * (2 * s * C / (exp eulerMascheroniConstant * l))) ≤
      (s * jr1965F s / (2 * exp eulerMascheroniConstant) + 6 * η) *
        (4 * C / l) := by
  let A := s * jr1965F s / (2 * exp eulerMascheroniConstant)
  let r := s * η / 4
  have hs0 : 0 ≤ s := by linarith
  have hE := exp_pos eulerMascheroniConstant
  have hA : A ≤ 4 := by
    dsimp [A]
    apply (div_le_iff₀ (by positivity : 0 < 2 * exp eulerMascheroniConstant)).2
    have hF := mul_le_mul_of_nonneg_left (jr1965F_le_delayConstant hs1) hs0
    unfold jr1965DelayConstant at hF
    nlinarith
  have hr : r ≤ η := by dsimp [r]; nlinarith
  have hr2 : r * (1 + η) ≤ 2 * η := by
    have h := mul_le_mul_of_nonneg_right hr (by linarith : 0 ≤ 1 + η)
    nlinarith [mul_nonneg hη (sub_nonneg.mpr hη1)]
  have hbudget : (A + r) * (1 + η) ≤ A + 6 * η := by
    nlinarith [mul_le_mul_of_nonneg_right hA hη]
  have heq :
      (jr1965F s + exp eulerMascheroniConstant * η / 2) *
          ((1 + η) * (2 * s * C / (exp eulerMascheroniConstant * l))) =
        ((A + r) * (1 + η)) * (4 * C / l) := by
    dsimp [A, r]
    field_simp
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hbudget (by positivity)

/-- Actual varying-level upper main sum on `[3/2,4]`, normalized by the
constructed canonical coefficient with a uniform additive error. -/
theorem wu_variable_upper_main_relative_extended (k : ℕ) (hk : 1 ≤ k) {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, Antitone V →
          (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
          ∀ s : ℝ, 3 / 2 ≤ s → s ≤ 4 →
          convolutionRosserMain N (convolutionWuWindows N Δ V) true
              (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) ≤
            (s * jr1965F s / (2 * exp eulerMascheroniConstant) + 6 * η) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let ρ := exp eulerMascheroniConstant * η / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨Z, hdensity⟩ := ordinaryRosser_upper_density_canonical_extended_local hρ
  obtain ⟨N1, hcut⟩ := wuLocalCutoff_eventually_large k hδ hδhi (max Z 2)
  obtain ⟨N2, hlocal⟩ := wu04_310_local_normalization k hk hδ hδhi hη
  refine ⟨max 2 (max N1 N2), ?_⟩
  intro N hN he i hik Δ hlo hhi V horder hV hprefix s hs hs4
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : N1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNlocal : N2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hs1 : 1 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  have hs10 : s ≤ 10 := by linarith
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hN2)
  have hpoint : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ordinaryRosserMainSum true N d (wuVariableRosserLevel N δ d)
          (wuLocalCutoff N δ d s) ≤
        (s * jr1965F s / (2 * exp eulerMascheroniConstant) + 6 * η) *
          (4 * wuSingularSeries (d * N) / log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by
    intro d hd
    have hg := wuVariableRosserLevel_geometry hN2 hδ hδhi hV hprefix hd hs1
    have hdne := (mem_boxConvolutionSupport.mp hd).ne'
    have hz := hcut N hN1 i Δ V hV hprefix d hd s hs1 hs10
    have hden := hdensity N d he (wuLocalCutoff N δ d s)
      ((N : ℝ) ^ (1 / 2 - δ) / d) s ((le_max_left _ _).trans hz)
      ((le_max_right _ _).trans hz) (by linarith [hg.2.1])
      hg.2.2.2.2.1.symm hs hs4
    have hnorm := hlocal N hNlocal he i hik Δ hlo hhi V horder hV
      ((boxSquaredPrefixes_iff _ _).mp hprefix) d hdne s hs1 hs10
    have hmainpos := wuLocal_main_pos hN2 hδ hδhi hV
      ((boxSquaredPrefixes_iff _ _).mp hprefix) hdne hs0
    have hprod :
        localSieveProduct (d * N) (wuLocalCutoff N δ d s) ≤
          (1 + η) * (2 * s * wuSingularSeries (d * N) /
            (exp eulerMascheroniConstant * log ((N : ℝ) ^ (1 / 2 - δ) / d))) := by
      apply (div_le_iff₀ hmainpos).mp
      linarith [(le_abs_self (_ : ℝ)).trans hnorm]
    have hF : 0 ≤ jr1965F s + ρ := add_nonneg (jr1965F_pos hs0).le hρ.le
    exact hden.trans ((mul_le_mul_of_nonneg_left hprod hF).trans
      (canonical_upper_extended_normalization_budget hs1 hs4
        (wuSingularSeries_pos _ (Nat.mul_pos hg.1 (by omega))).le
        (log_pos hg.2.1) hη.le hη1))
  unfold convolutionRosserMain boxTheta
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro d hd
  have h := mul_le_mul_of_nonneg_left (hpoint d hd)
    (mul_nonneg (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d))
      (div_nonneg hli (Nat.cast_nonneg (Nat.totient d))))
  convert h using 1 <;> ring

/-- Actual source upper comparison on `[1,4]`, with both strict and printed
closed conventions. Below `3/2` only the existing finite-monotonicity baseline
is used. Above three the coefficient is not replaced by one. -/
theorem wu_boxPhi_upper_source_extended (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, Antitone V →
          (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
          ∀ s : ℝ, 1 ≤ s → s ≤ 4 →
          wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
              (s * jr1965F s / (2 * exp eulerMascheroniConstant) + ε) *
                boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ∧
          wuBoxPhiLE N δ (convolutionWuWindows N Δ V) s ≤
              (s * jr1965F s / (2 * exp eulerMascheroniConstant) + ε) *
                boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let η : ℝ := min 1 (ε / 7)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : 7 * η ≤ ε := by have := min_le_right 1 (ε / 7); dsimp [η]; linarith
  obtain ⟨N1, hmain⟩ := wu_variable_upper_main_relative_extended k hk hδ hδhi hη hη1
  obtain ⟨N2, hrem⟩ := wu_variable_level_remainder_relative k hδ hδhi hη
  obtain ⟨N3, hbase⟩ := wu_boxPhi_upper_source k hk hδ hδhi hε
  refine ⟨max 2 (max N1 (max N2 N3)), ?_⟩
  intro N hN he i hik Δ hlo hhi V horder hV hprefix s hs hs4
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : N1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNr : N2 ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNb : N3 ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  suffices hstrict :
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        (s * jr1965F s / (2 * exp eulerMascheroniConstant) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) from
    ⟨hstrict, (wuBoxPhiLE_le_strict N δ _ s).trans hstrict⟩
  by_cases hslo : 3 / 2 ≤ s
  · have hM := hmain N hN1 he i hik Δ hlo hhi V horder hV hprefix s hslo hs4
    have hR := hrem N hNr i hik Δ hlo hhi V hV hprefix true
      (fun d => wuLocalCutoff N δ d s)
    have hT : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
        (convolutionWuWindows N Δ V) :=
      nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hR) hη
    have hfinite :
        wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
          convolutionRosserMain N (convolutionWuWindows N Δ V) true
            (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) +
          convolutionRosserRemainder N (convolutionWuWindows N Δ V) true
            (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) := by
      unfold wuBoxPhi convolutionSieveCount convolutionRosserMain convolutionRosserRemainder
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro d hd
      have hg := wuVariableRosserLevel_geometry hN2 hδ hδhi hV hprefix hd hs
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left
        (ordinaryRosser_upper_finite hg.2.2.1 hg.2.2.2.1) (Nat.cast_nonneg _)
    have hr := (le_abs_self _).trans hR
    have hpay := mul_le_mul_of_nonneg_right hηε hT
    nlinarith
  · have hs3 : s ≤ 3 := by linarith
    rw [jr1965F_normalized_initial (by linarith) hs3]
    exact (hbase N hNb he i hik Δ hlo hhi V horder hV hprefix s hs hs3).1

end Wu2008DoubleSieve
