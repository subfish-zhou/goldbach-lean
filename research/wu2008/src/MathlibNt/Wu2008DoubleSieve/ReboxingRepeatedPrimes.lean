import MathlibNt.Wu2008DoubleSieve.ReboxingNormalization

/-!
# A same-fibre payment for repeated inserted primes

The rectangular reboxing windows may include p dividing d. The normalized
positive majorant below contains that whole lane, not just the smaller
local-factor discrepancy. Distinct large prime divisors have bounded
cardinality even when the original convolution has repetitions.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem reboxing_log_ratio_half {q p : ℝ} (hq : 1 < q) (hp : 0 < p)
    (hupper : p ≤ q ^ (1 / 2 : ℝ)) :
    1 / 2 ≤ 1 - log p / log q := by
  have hlq : 0 < log q := log_pos hq
  have hlog := log_le_log hp hupper
  rw [log_rpow (by linarith : 0 < q)] at hlog
  have hdiv : log p / log q ≤ 1 / 2 :=
    (div_le_iff₀ hlq).2 (by linarith)
  linarith

theorem reboxing_prime_weight_le_four_div {q p : ℝ} (hq : 1 < q)
    (hp : 4 ≤ p) (hupper : p ≤ q ^ (1 / 2 : ℝ)) :
    0 ≤ 1 / ((p - 2) * (1 - log p / log q)) ∧
      1 / ((p - 2) * (1 - log p / log q)) ≤ 4 / p := by
  have hlog := reboxing_log_ratio_half hq (by linarith : 0 < p) hupper
  have hden : 0 < (p - 2) * (1 - log p / log q) :=
    mul_pos (by linarith) (by linarith)
  refine ⟨by positivity, (div_le_div_iff₀ hden (by linarith : 0 < p)).2 ?_⟩
  nlinarith [mul_nonneg (by linarith : 0 ≤ p - 2)
    (by linarith : 0 ≤ 1 - log p / log q - 1 / 2)]

/-- Uniform finite prime-divisor payment in one actual d fibre.
The complete positive rectangular lane is bounded, not merely its
C/phi discrepancy. -/
theorem reboxing_repeated_prime_sum_le {N d : ℕ} {q η : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hdN : d ≤ N) (hη : 0 < η)
    (hlarge : 4 ≤ (N : ℝ) ^ η) (hq : 1 < q) :
    (∑ p ∈ (primeWindow N ((N : ℝ) ^ η) (q ^ (1 / 2 : ℝ))).filter (fun p => p ∣ d),
        1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log q))) ≤
      4 / (η * (N : ℝ) ^ η) := by
  let P := (primeWindow N ((N : ℝ) ^ η) (q ^ (1 / 2 : ℝ))).filter (fun p => p ∣ d)
  have hY : 0 < (N : ℝ) ^ η := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hsub : P ⊆ largePrimeDivisors d ((N : ℝ) ^ η) := by
    intro p hp
    obtain ⟨hp, hpd⟩ := mem_filter.mp hp
    obtain ⟨hpp, _, hlo, _⟩ := mem_primeWindow.mp hp
    exact mem_largePrimeDivisors.mpr ⟨hpp, hpd, hd.ne', hlo⟩
  have hc : (P.card : ℝ) ≤ (largePrimeDivisors d ((N : ℝ) ^ η)).card := by
    exact_mod_cast card_le_card hsub
  have hcard : (P.card : ℝ) ≤ 1 / η :=
    hc.trans (largePrimeDivisors_card_le_inv hN hd hdN hη)
  calc
    _ ≤ ∑ _p ∈ P, 4 / (N : ℝ) ^ η := by
      apply sum_le_sum
      intro p hp
      have hwin := mem_primeWindow.mp (mem_filter.mp hp).1
      have hp4 : (4 : ℝ) ≤ p := hlarge.trans hwin.2.2.1
      exact (reboxing_prime_weight_le_four_div hq hp4 hwin.2.2.2.le).2.trans
        (div_le_div_of_nonneg_left (by norm_num) hY hwin.2.2.1)
    _ = (P.card : ℝ) * (4 / (N : ℝ) ^ η) := by simp
    _ ≤ (1 / η) * (4 / (N : ℝ) ^ η) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- Literal positive majorant for every repeated inserted prime below
the admissible square-root cutoff. -/
noncomputable def reboxingRepeatedTheta {i : ℕ} (N : ℕ) (Q η : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport W,
      ((convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log (Q / d))) *
      ∑ p ∈ (primeWindow N ((N : ℝ) ^ η) ((Q / d) ^ (1 / 2 : ℝ))).filter (fun p => p ∣ d),
        1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))

/-- The source mass cancels fibre by fibre. There is no loss of
log(N)^(5k) from dividing by a global lower bound for Theta. -/
theorem reboxingRepeatedTheta_le {i N : ℕ} {Q η : ℝ} {W : Fin i → Finset ℕ}
    (hN : 4 ≤ N) (hη : 0 < η) (hlarge : 4 ≤ (N : ℝ) ^ η)
    (hsupport : ∀ d ∈ boxConvolutionSupport W, 0 < d ∧ d ≤ N ∧ 1 < Q / d) :
    reboxingRepeatedTheta N Q η W ≤
      (4 / (η * (N : ℝ) ^ η)) * boxTheta N Q W := by
  have hli : 0 ≤ logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans (box_trueLi_lower hN)
  unfold reboxingRepeatedTheta boxTheta
  rw [mul_left_comm (4 / (η * (N : ℝ) ^ η))]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 4 * logarithmicIntegral N)
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  have hs := hsupport d hd
  have hw : 0 ≤ (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
      ((Nat.totient d : ℝ) * log (Q / d)) := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (wuSingularSeries_pos _ (Nat.mul_pos hs.1 (by omega))).le)
      (mul_nonneg (Nat.cast_nonneg _) (log_pos hs.2.2).le)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (reboxing_repeated_prime_sum_le (show 1 < N by omega) hs.1 hs.2.1 hη hlarge hs.2.2) hw

/-- Fixed k, delta and eta precede epsilon and the single threshold;
all actual source boxes are then admitted, including depth zero. -/
theorem wu_reboxing_repeated_theta_relative (k : ℕ) {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        reboxingRepeatedTheta N ((N : ℝ) ^ (1 / 2 - δ)) η (convolutionWuWindows N Δ V) ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have ht := (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop, max 4 (4 / (η * ε)) ≤ (N : ℝ) ^ η :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hevent
  refine ⟨max 4 N0, ?_⟩
  intro N hN i Δ V hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hlarge := hN0 N ((le_max_right _ _).trans hN)
  have hs : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      0 < d ∧ d ≤ N ∧ 1 < (N : ℝ) ^ (1 / 2 - δ) / d := by
    intro d hd
    have hd' := wuLocal_support_bounds (show 1 ≤ N by omega)
      hδ hδhi hb.2.2.2.2.1 ((boxSquaredPrefixes_iff _ _).mp hb.2.2.2.2.2) hd
    refine ⟨hd'.1, hd'.2.1, ?_⟩
    exact (one_lt_rpow (by exact_mod_cast (show 1 < N by omega))
      (wuLocalExponent_pos k hδ hδhi)).trans_le hd'.2.2
  have hT : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
    unfold boxTheta
    apply mul_nonneg
    · have hli := box_trueLi_lower hN4
      have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
      have hli0 : 0 ≤ logarithmicIntegral N :=
        (div_nonneg (Nat.cast_nonneg N) (mul_nonneg (by norm_num) hl.le)).trans hli
      exact mul_nonneg (by norm_num) hli0
    · apply sum_nonneg
      intro d hd
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (wuSingularSeries_pos _ (Nat.mul_pos (hs d hd).1 (by omega))).le)
        (mul_nonneg (Nat.cast_nonneg _) (log_pos (hs d hd).2.2).le)
  have hcoef : 4 / (η * (N : ℝ) ^ η) ≤ ε := by
    have hY : 0 < (N : ℝ) ^ η := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
    apply (div_le_iff₀ (mul_pos hη hY)).2
    have hh := (div_le_iff₀ (mul_pos hη hε)).1 ((le_max_right _ _).trans hlarge)
    nlinarith [hh]
  exact (reboxingRepeatedTheta_le hN4 hη ((le_max_left _ _).trans hlarge) hs).trans
    (mul_le_mul_of_nonneg_right hcoef hT)

end Wu2008DoubleSieve
