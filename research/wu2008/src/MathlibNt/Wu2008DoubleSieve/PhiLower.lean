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


end Wu2008DoubleSieve
