import MathlibNt.Wu2008DoubleSieve.VariableLevelGeometry
import MathlibNt.Wu2008DoubleSieve.CanonicalUpperDensity

/-!
# Actual Phi/Theta upper comparison on the canonical base interval

Source objects: Wu08 (3.1), (3.4), (3.5), with Wu04's strict sifting
convention. Printed Wu08 closed sifting is distinguished in `PhiMonotone`.
This is the standard-sieve
baseline, not a positive double-sieve improvement. One Rosser level `Q/d`
per fibre gives the exact density parameter `s`. Its signed ordinary AP
remainder is already paid relative to the actual Theta.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- The strict-convention source Phi, with ordered convolution multiplicity
and unscaled `P(d*N)` sifting at its actual moving cutoff. -/
noncomputable def wuBoxPhi {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (s : ℝ) : ℝ :=
  convolutionSieveCount N W (fun d => wuLocalCutoff N δ d s)

theorem wuBoxPhi_eq_tuple_sum {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (s : ℝ) :
    wuBoxPhi N δ W s =
      ∑ t ∈ Fintype.piFinset W,
        (sourceSieveCount N (∏ j, t j) ((∏ j, t j) * N)
          (wuLocalCutoff N δ (∏ j, t j) s) : ℝ) :=
  boxConvolution_sum_fibres W _

theorem wuBoxPhi_nonneg {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (s : ℝ) : 0 ≤ wuBoxPhi N δ W s := by
  unfold wuBoxPhi convolutionSieveCount sourceSieveCount
  apply sum_nonneg
  intro d _
  positivity

/-- The canonical coefficient is derived, not an arbitrary named `A(s)`.
The two relative main-term losses cost at most `(1+eta)^2`. -/
theorem canonical_upper_normalization_budget {s C l η : ℝ}
    (hs : 0 < s) (hs3 : s ≤ 3) (hC : 0 ≤ C) (hl : 0 < l) (hη : 0 ≤ η) :
    (jr1965F s + 2 * exp eulerMascheroniConstant * η / 3) *
        ((1 + η) * (2 * s * C / (exp eulerMascheroniConstant * l))) ≤
      (1 + η) ^ 2 * (4 * C / l) := by
  rw [jr1965F_eq_of_le_three hs3]
  have hE := exp_pos eulerMascheroniConstant
  have heq :
      (2 * exp eulerMascheroniConstant / s +
          2 * exp eulerMascheroniConstant * η / 3) *
        ((1 + η) * (2 * s * C / (exp eulerMascheroniConstant * l))) =
      (1 + s * η / 3) * (1 + η) * (4 * C / l) := by
    field_simp
    ring
  rw [heq, pow_two, mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_right
  · nlinarith [mul_le_mul_of_nonneg_right hs3 hη]
  · positivity

/-- The actual varying-level Rosser main sum has the right normalization,
uniformly before every source box and every `s` in `[3/2,3]`. -/
theorem wu_variable_upper_main_relative (k : ℕ) (hk : 1 ≤ k) {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, Antitone V →
          (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
          ∀ s : ℝ, 3 / 2 ≤ s → s ≤ 3 →
          convolutionRosserMain N (convolutionWuWindows N Δ V) true
              (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) ≤
            (1 + η) ^ 2 *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let ρ : ℝ := 2 * exp eulerMascheroniConstant * η / 3
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨Z, hdensity⟩ := ordinaryRosser_upper_density_canonical hρ
  obtain ⟨N1, hcut⟩ := wuLocalCutoff_eventually_large k hδ hδhi (max Z 2)
  obtain ⟨N2, hlocal⟩ := wu04_310_local_normalization k hk hδ hδhi hη
  refine ⟨max 2 (max N1 N2), ?_⟩
  intro N hN he i hik Δ hlo hhi V horder hV hprefix s hs hs3
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
        (1 + η) ^ 2 *
          (4 * wuSingularSeries (d * N) / log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by
    intro d hd
    have hgeom := wuVariableRosserLevel_geometry hN2 hδ hδhi hV hprefix hd hs1
    have hdne := (mem_boxConvolutionSupport.mp hd).ne'
    have hz := hcut N hN1 i Δ V hV hprefix d hd s hs1 hs10
    have hden := hdensity N d he (wuLocalCutoff N δ d s)
      ((N : ℝ) ^ (1 / 2 - δ) / d) s ((le_max_left _ _).trans hz)
      ((le_max_right _ _).trans hz) (by linarith [hgeom.2.1])
      hgeom.2.2.2.2.1.symm hs hs3
    have heuler :
        (∏ p ∈ primeWindow (d * N) 0 (wuLocalCutoff N δ d s),
          (1 - 1 / ((p : ℝ) - 1))) =
          localSieveProduct (d * N) (wuLocalCutoff N δ d s) := by
      rw [localSieveProduct, localSievePrimes_eq_primeWindow]
    rw [heuler] at hden
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
    have hF : 0 ≤ jr1965F s + ρ := by
      rw [jr1965F_eq_of_le_three hs3]
      positivity
    exact hden.trans ((mul_le_mul_of_nonneg_left hprod hF).trans
      (canonical_upper_normalization_budget hs0 hs3
        (wuSingularSeries_pos _ (Nat.mul_pos hgeom.1 (by omega))).le
        (log_pos hgeom.2.1) hη.le))
  unfold convolutionRosserMain boxTheta
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro d hd
  have h := mul_le_mul_of_nonneg_left (hpoint d hd)
    (mul_nonneg (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d))
      (div_nonneg hli (Nat.cast_nonneg (Nat.totient d))))
  convert h using 1 <;> ring

/-- Unconditional standard-sieve baseline for the actual Phi. The
coefficient is `A(s)=1` on this canonical base interval. -/
theorem wu_boxPhi_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, Antitone V →
          (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
          ∀ s : ℝ, 3 / 2 ≤ s → s ≤ 3 →
          wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
            (1 + ε) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
              (convolutionWuWindows N Δ V) := by
  let η : ℝ := min 1 (ε / 4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / 4 := min_le_right _ _
  obtain ⟨N1, hmain⟩ := wu_variable_upper_main_relative k hk hδ hδhi hη
  obtain ⟨N2, hrem⟩ := wu_variable_level_remainder_relative k hδ hδhi hη
  refine ⟨max 2 (max N1 N2), ?_⟩
  intro N hN he i hik Δ hlo hhi V horder hV hprefix s hs hs3
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : N1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNrem : N2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hM := hmain N hN1 he i hik Δ hlo hhi V horder hV hprefix s hs hs3
  have hR := hrem N hNrem i hik Δ hlo hhi V hV hprefix true
    (fun d => wuLocalCutoff N δ d s)
  have hT : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
      (convolutionWuWindows N Δ V) := by
    have := (abs_nonneg _).trans hR
    exact nonneg_of_mul_nonneg_right this hη
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
    have hg := wuVariableRosserLevel_geometry hN2 hδ hδhi hV hprefix hd
      (by linarith : 1 ≤ s)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left
      (ordinaryRosser_upper_finite hg.2.2.1 hg.2.2.2.1) (Nat.cast_nonneg _)
  have hbudget : (1 + η) ^ 2 + η ≤ 1 + ε := by
    nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hη1)]
  calc
    _ ≤ ((1 + η) ^ 2 + η) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
      have hr := (le_abs_self _).trans hR
      nlinarith [hfinite, hM]
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hT

end Wu2008DoubleSieve
