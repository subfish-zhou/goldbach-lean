import MathlibNt.Wu2008DoubleSieve.BoxMassConvolution
import MathlibNt.Wu2008DoubleSieve.Normalization

/-!
# The actual Theta lower bound, Wu (2004), (3.7)

The denominator is `log(Q/d)` and the singular series is `C(d*N)`.
The genuine squared-prefix inequalities imply the support bounds needed
here; no positivity of Theta or nonempty-window assertion is assumed.
-/

namespace Wu2008DoubleSieve

open Finset Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.SingularSeries

noncomputable def boxTheta {i : ℕ} (N : ℕ) (Q : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport W,
      (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * Real.log (Q / d))

theorem boxTheta_zero_depth (N : ℕ) (Q : ℝ) (W : Fin 0 → Finset ℕ) :
    boxTheta N Q W = 4 * logarithmicIntegral N * wuSingularSeries N / Real.log Q := by
  simp [boxTheta, boxConvolutionSupport, convolutionCoeff_zero_depth, Fintype.piFinset]
  ring

theorem box_trueLi_lower {N : ℕ} (hN : 4 ≤ N) :
    (N : ℝ) / (2 * Real.log N) ≤ logarithmicIntegral N := by
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hli := box_trueLi_sub_lower (show (2 : ℝ) ≤ N / 2 by linarith)
    (show (N : ℝ) / 2 ≤ N by linarith)
  have hpos : 0 ≤ logarithmicIntegral ((N : ℝ) / 2) :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by linarith)
  have heq : ((N : ℝ) - N / 2) / Real.log N = N / (2 * Real.log N) := by ring
  linarith

/-- Finite comparison with the actual singular series and true logarithmic
integral. The subsequent source-family theorem proves the support conditions. -/
theorem boxTheta_lower_of_support {i N : ℕ} {Q : ℝ}
    (W : Fin i → Finset ℕ) (hN : 4 ≤ N)
    (hpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hQ : ∀ d ∈ boxConvolutionSupport W, 1 < Q / d ∧ Q / d ≤ N) :
    2 * liuUniversalProduct * (N : ℝ) / Real.log N ^ 2 *
      boxConvolutionReciprocalMass W ≤ boxTheta N Q W := by
  have hU := liuUniversalProduct_pos
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmass : 0 ≤ boxConvolutionReciprocalMass W :=
    sum_nonneg (fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d))
  have hli := box_trueLi_lower hN
  have hli0 : 0 ≤ logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N / (2 * Real.log N)).trans hli
  have hsum :
      liuUniversalProduct / Real.log N * boxConvolutionReciprocalMass W ≤
        ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
            ((Nat.totient d : ℝ) * Real.log (Q / d)) := by
    unfold boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hd0 := hpos d hd
    have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
    have ht0 : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
    have ht : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
    have hu0 : 0 < Real.log (Q / d) := Real.log_pos (hQ d hd).1
    have hu : Real.log (Q / d) ≤ Real.log N :=
      Real.log_le_log (by linarith [(hQ d hd).1]) (hQ d hd).2
    have hC : liuUniversalProduct ≤ wuSingularSeries (d * N) := by
      rw [wuSingularSeries_eq_liu _ (Nat.mul_pos hd0 (by omega))]
      exact liuUniversalProduct_le_liuSingularSeries _
    have hC0 : 0 < wuSingularSeries (d * N) := hU.trans_le hC
    calc
      _ = (convolutionCoeff W d : ℝ) * liuUniversalProduct /
          ((d : ℝ) * Real.log N) := by ring
      _ ≤ _ := by
        gcongr
  calc
    _ = 4 * ((N : ℝ) / (2 * Real.log N)) *
        (liuUniversalProduct / Real.log N * boxConvolutionReciprocalMass W) := by ring
    _ ≤ 4 * logarithmicIntegral N *
        (liuUniversalProduct / Real.log N * boxConvolutionReciprocalMass W) := by
      gcongr
    _ ≤ boxTheta N Q W := by
      exact mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hli0)

/-- The source's squared-prefix condition, with real endpoints and the
empty product equal to one. This is exactly the family of inequalities
`V₁² ≤ Q`, `V₁V₂² ≤ Q`, ... . -/
def boxSquaredPrefixes {i : ℕ} (Q : ℝ) (V : Fin i → ℝ) : Prop :=
  ∀ j, (∏ l ∈ univ.filter (fun l : Fin i => l < j), V l) * (V j) ^ 2 ≤ Q

theorem boxSquaredPrefixes_upper {i : ℕ} {Q T : ℝ} {V : Fin i → ℝ}
    (hV : ∀ j, 1 ≤ V j) (hprefix : boxSquaredPrefixes Q V) (hQT : Q ≤ T) :
    ∀ j, V j ≤ T := by
  intro j
  have hp : 1 ≤ ∏ l ∈ univ.filter (fun l : Fin i => l < j), V l :=
    one_le_prod (fun l _ => hV l)
  have hsq : (V j) ^ 2 ≤ Q := by
    have := hprefix j
    nlinarith [sq_nonneg (V j)]
  exact (by nlinarith [hV j] : V j ≤ (V j) ^ 2).trans (hsq.trans hQT)

/-- The last squared prefix pays one further lower-prime factor.
This is used only at positive depth; depth zero is handled separately. -/
theorem boxSquaredPrefixes_product_mul_lower {i : ℕ} (hi : 0 < i)
    {Q w : ℝ} {V : Fin i → ℝ} (hw : 0 ≤ w)
    (hV : ∀ j, w ≤ V j) (hprefix : boxSquaredPrefixes Q V) :
    (∏ j, V j) * w ≤ Q := by
  let r : Fin i := ⟨i - 1, by omega⟩
  have hr : univ.filter (fun l : Fin i => l < r) = univ.erase r := by
    ext l
    simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    have hl := l.isLt
    change l.val < i - 1 ↔ l ≠ r
    constructor
    · intro h he
      subst l
      simp [r] at h
    · intro h
      have hn : l.val ≠ i - 1 := by
        intro he
        exact h (Fin.ext he)
      omega
  have hpr := hprefix r
  rw [hr] at hpr
  have heq : (∏ j, V j) * V r =
      (∏ l ∈ univ.erase r, V l) * (V r) ^ 2 := by
    rw [← prod_erase_mul _ _ (mem_univ r)]
    ring
  calc
    _ ≤ (∏ j, V j) * V r :=
      mul_le_mul_of_nonneg_left (hV r) (prod_nonneg (fun j _ => hw.trans (hV j)))
    _ ≤ Q := by rwa [heq]

/-- Actual support lies in `1 < Q/d ≤ N` under the source's squared prefixes.
The unit convolution at depth zero uses `1 < Q` directly. -/
theorem boxSquaredPrefixes_support {i N : ℕ} {Q w Δ : ℝ} {V : Fin i → ℝ}
    (hw : 1 < w) (hQ : 1 < Q) (hQN : Q ≤ N)
    (hV : ∀ j, w ≤ V j) (hprefix : boxSquaredPrefixes Q V)
    {d : ℕ} (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 < d ∧ 1 < Q / d ∧ Q / d ≤ N := by
  have hd0 : 0 < d :=
    boxConvolutionSupport_pos (fun j p hp => (mem_convolutionWuWindows.mp hp).1.pos) hd
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hdprod := boxConvolutionSupport_le_product
    (fun j p hp => (mem_convolutionWuWindows.mp hp).2.2.2.le) hd
  refine ⟨hd0, ?_, ?_⟩
  · by_cases hi : i = 0
    · subst i
      have hdle : (d : ℝ) ≤ 1 := by simpa using hdprod
      have hdeq : (d : ℝ) = 1 := le_antisymm hdle hd1
      simpa only [hdeq, div_one] using hQ
    · have hp := boxSquaredPrefixes_product_mul_lower (Nat.pos_of_ne_zero hi)
        (by linarith : 0 ≤ w) hV hprefix
      have hpay : (d : ℝ) * w ≤ Q :=
        (mul_le_mul_of_nonneg_right hdprod (by linarith)).trans hp
      exact hw.trans_le ((le_div_iff₀ hd0').mpr (by nlinarith [hpay]))
  · apply (div_le_iff₀ hd0').mpr
    exact hQN.trans (by nlinarith [show (0 : ℝ) ≤ N by positivity])

/-- Wu (3.7), with all constants before every depth, `Δ`, and endpoint.
The source's ordering may be imposed in addition; the proof only needs
its genuine squared-prefix constraints and fixed lower-prime cutoff. -/
theorem wu_boxTheta_lower (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + Real.log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * Real.log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
          c * (N : ℝ) / Real.log N ^ (5 * k + 2) ≤
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let α := δ ^ (k + 1)
  have hα : 0 < α := pow_pos hδ _
  have hU := liuUniversalProduct_pos
  obtain ⟨N₁, hmass⟩ := wu_boxConvolution_mass_bounds k hα
  refine ⟨2 * liuUniversalProduct * (1 / 12 : ℝ) ^ k,
    by positivity, max 4 N₁, ?_⟩
  intro N hN i hik Δ hΔlo hΔhi V hV hprefix
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hw : 1 < (N : ℝ) ^ α := Real.one_lt_rpow hN1 hα
  have hQ : 1 < (N : ℝ) ^ (1 / 2 - δ) :=
    Real.one_lt_rpow hN1 (by linarith)
  have hQN : (N : ℝ) ^ (1 / 2 - δ) ≤ N := by
    calc
      _ ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
      _ = _ := Real.rpow_one _
  have hupper := boxSquaredPrefixes_upper (fun j => hw.le.trans (hV j)) hprefix hQN
  have hmasslo := (hmass N ((le_max_right _ _).trans hN)
    i hik Δ hΔlo hΔhi V hV hupper).1
  have hs := fun d hd => boxSquaredPrefixes_support hw hQ hQN hV hprefix
    (Δ := Δ) (d := d) hd
  have htheta := boxTheta_lower_of_support (convolutionWuWindows N Δ V) hN4
    (fun d hd => (hs d hd).1) (fun d hd => (hs d hd).2)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  calc
    _ = (2 * liuUniversalProduct * (N : ℝ) / Real.log N ^ 2) *
        ((1 / 12 : ℝ) ^ k / Real.log N ^ (5 * k)) := by
      rw [pow_add]
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hmasslo (by positivity)).trans htheta

end Wu2008DoubleSieve
