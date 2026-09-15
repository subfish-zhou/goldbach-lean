import MathlibNt.Wu2008DoubleSieve.CanonicalLowerDensity
import MathlibNt.Wu2008DoubleSieve.PhiEndpoint

/-!
# Actual canonical lower Phi, with the printed endpoints paid

The genuine lower-density producer on `[2,4]`, the source local product,
and the varying-level signed remainder give a nonzero lower baseline.
The strict/closed endpoint is paid separately. The zero branch extends
the source-facing conclusion to `[1,4]`. No positive h gain is asserted.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- A sign-safe local normalization. In particular `f(s)-rho` is allowed
to be negative near `s=2`; no positive lower-density factor is assumed. -/
theorem canonical_lower_normalization_budget {s C l η V : ℝ}
    (hs2 : 2 ≤ s) (hs4 : s ≤ 4) (hC : 0 < C) (hl : 0 < l)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hV : |V / (2 * s * C / (exp eulerMascheroniConstant * l)) - 1| ≤ η) :
    (log (s - 1) - 4 * η) * (4 * C / l) ≤
      (jr1965f s - exp eulerMascheroniConstant * η / 2) * V := by
  let M := 2 * s * C / (exp eulerMascheroniConstant * l)
  let B := 4 * C / l
  let a := log (s - 1)
  let r := s * η / 4
  have hs0 : 0 < s := by linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  change |V / M - 1| ≤ η at hV
  have hlo : (1 - η) * M ≤ V := by
    apply (le_div_iff₀ hM).mp
    linarith [(abs_le.mp hV).1]
  have hhi : V ≤ (1 + η) * M := by
    apply (div_le_iff₀ hM).mp
    linarith [(abs_le.mp hV).2]
  have ha2 : a ≤ 2 := by
    have h := log_le_sub_one_of_pos (show 0 < s - 1 by linarith)
    dsimp [a]
    linarith
  have hr : r ≤ η := by dsimp [r]; nlinarith
  have hprod : (1 + η) * r ≤ 2 * η := by
    have := mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ 1 + η)
    nlinarith [mul_nonneg hη (sub_nonneg.mpr hη1)]
  have hbudget : a - 4 * η ≤ a * (1 - η) - r * (1 + η) := by
    nlinarith [mul_le_mul_of_nonneg_right ha2 hη]
  have hfM : jr1965f s * M = a * B := by
    rw [jr1965f_eq_log_firstInterval hs2 hs4]
    dsimp [M, a, B]
    field_simp
    ring
  have hrM : (exp eulerMascheroniConstant * η / 2) * M = r * B := by
    dsimp [M, r, B]
    field_simp
  have hfl := mul_le_mul_of_nonneg_left hlo (jr1965f_nonneg hs0)
  have hrh := mul_le_mul_of_nonneg_left hhi
    (show 0 ≤ exp eulerMascheroniConstant * η / 2 by positivity)
  have hfirst : (a * (1 - η) - r * (1 + η)) * B ≤
      (jr1965f s - exp eulerMascheroniConstant * η / 2) * V := by
    calc
      _ = jr1965f s * ((1 - η) * M) -
          (exp eulerMascheroniConstant * η / 2) * ((1 + η) * M) := by
        calc
          _ = (1 - η) * (a * B) - (1 + η) * (r * B) := by ring
          _ = _ := by rw [← hfM, ← hrM]; ring
      _ ≤ _ := by nlinarith
  exact (mul_le_mul_of_nonneg_right hbudget hB.le).trans hfirst

/-- The actual lower main term on every source box, before its signed
remainder. The coefficient `log(s-1)` is the constructed canonical a(s). -/
theorem wu_variable_lower_main_relative (k : ℕ) (hk : 1 ≤ k) {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, Antitone V →
          (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
          ∀ s : ℝ, 2 ≤ s → s ≤ 4 →
          (log (s - 1) - 4 * η) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
            convolutionRosserMain N (convolutionWuWindows N Δ V) false
              (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) := by
  let ρ := exp eulerMascheroniConstant * η / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨Z, hdensity⟩ := ordinaryRosser_lower_density_canonical_local hρ
  obtain ⟨N1, hcut⟩ := wuLocalCutoff_eventually_large k hδ hδhi (max Z 2)
  obtain ⟨N2, hlocal⟩ := wu04_310_local_normalization k hk hδ hδhi hη
  refine ⟨max 2 (max N1 N2), ?_⟩
  intro N hN he i hik Δ hlo hhi V horder hV hprefix s hs hs4
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : N1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNlocal : N2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hs1 : 1 ≤ s := by linarith
  have hs10 : s ≤ 10 := by linarith
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hN2)
  have hpoint : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (log (s - 1) - 4 * η) *
          (4 * wuSingularSeries (d * N) / log ((N : ℝ) ^ (1 / 2 - δ) / d)) ≤
        ordinaryRosserMainSum false N d (wuVariableRosserLevel N δ d)
          (wuLocalCutoff N δ d s) := by
    intro d hd
    have hg := wuVariableRosserLevel_geometry hN2 hδ hδhi hV hprefix hd hs1
    have hz := hcut N hN1 i Δ V hV hprefix d hd s hs1 hs10
    have hden := hdensity N d he (wuLocalCutoff N δ d s)
      ((N : ℝ) ^ (1 / 2 - δ) / d) s ((le_max_left _ _).trans hz)
      ((le_max_right _ _).trans hz) (by linarith [hg.2.1])
      hg.2.2.2.2.1.symm hs hs4
    have hnorm := hlocal N hNlocal he i hik Δ hlo hhi V horder hV
      ((boxSquaredPrefixes_iff _ _).mp hprefix) d
      (mem_boxConvolutionSupport.mp hd).ne' s hs1 hs10
    exact (canonical_lower_normalization_budget hs hs4
      (wuSingularSeries_pos _ (Nat.mul_pos hg.1 (by omega)))
      (log_pos hg.2.1) hη.le hη1 hnorm).trans hden
  unfold boxTheta convolutionRosserMain
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro d hd
  have h := mul_le_mul_of_nonneg_left (hpoint d hd)
    (mul_nonneg (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d))
      (div_nonneg hli (Nat.cast_nonneg (Nat.totient d))))
  convert h using 1 <;> ring

/-- Actual printed-Wu08 lower Phi, with the endpoint and signed errors
both paid. The canonical zero branch includes `[1,2]`; the nonzero
branch is proved on `(2,4]`. No h/H improvement is assumed. -/
theorem wu_boxPhi_lower_source (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, Antitone V →
          (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
          ∀ s : ℝ, 1 ≤ s → s ≤ 4 →
          (s * jr1965f s / (2 * exp eulerMascheroniConstant) - ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
            wuBoxPhiLE N δ (convolutionWuWindows N Δ V) s ∧
          (s * jr1965f s / (2 * exp eulerMascheroniConstant) - ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
            wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
  let η : ℝ := min 1 (ε / 6)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / 6 := min_le_right _ _
  obtain ⟨N1, hmain⟩ := wu_variable_lower_main_relative k hk hδ hδhi hη hη1
  obtain ⟨N2, hrem⟩ := wu_variable_level_remainder_relative k hδ hδhi hη
  obtain ⟨N3, hend⟩ := wu_boxPhi_endpoint_relative k hδ hδhi hη
  refine ⟨max 2 (max N1 (max N2 N3)), ?_⟩
  intro N hN he i hik Δ hlo hhi V horder hV hprefix s hs hs4
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : N1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNr : N2 ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNe : N3 ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hR := hrem N hNr i hik Δ hlo hhi V hV hprefix false
    (fun d => wuLocalCutoff N δ d s)
  have hT : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
      (convolutionWuWindows N Δ V) :=
    nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hR) hη
  suffices hclosed :
      (s * jr1965f s / (2 * exp eulerMascheroniConstant) - ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhiLE N δ (convolutionWuWindows N Δ V) s from
    ⟨hclosed, hclosed.trans (wuBoxPhiLE_le_strict N δ _ s)⟩
  by_cases hs2 : s ≤ 2
  · rw [jr1965f_initial hs2, mul_zero, zero_div, zero_sub]
    have hnonneg : 0 ≤ wuBoxPhiLE N δ (convolutionWuWindows N Δ V) s := by
      unfold wuBoxPhiLE sourceSieveCountLE
      exact sum_nonneg (fun _ _ => by positivity)
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hT).trans hnonneg
  have hs2' : 2 ≤ s := (lt_of_not_ge hs2).le
  rw [jr1965f_normalized_firstInterval hs2' hs4]
  have hM := hmain N hN1 he i hik Δ hlo hhi V horder hV hprefix s hs2' hs4
  have hE := (hend N hNe he i hik Δ hlo hhi V hV hprefix s hs (by linarith)).2
  have hfinite :
      convolutionRosserMain N (convolutionWuWindows N Δ V) false
          (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) +
        convolutionRosserRemainder N (convolutionWuWindows N Δ V) false
          (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
    unfold wuBoxPhi convolutionSieveCount convolutionRosserMain convolutionRosserRemainder
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    have hg := wuVariableRosserLevel_geometry hN2 hδ hδhi hV hprefix hd hs
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left
      (ordinaryRosser_lower_finite hg.2.2.2.1) (Nat.cast_nonneg _)
  have hneg := neg_abs_le (convolutionRosserRemainder N (convolutionWuWindows N Δ V)
    false (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s))
  have hpay : (6 * η) *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
    mul_le_mul_of_nonneg_right (by linarith) hT
  nlinarith

end Wu2008DoubleSieve
