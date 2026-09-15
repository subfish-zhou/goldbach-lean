import MathlibNt.Wu2008DoubleSieve.ReboxingPrimeIntegral
import MathlibNt.Wu2008DoubleSieve.ReboxingEffectiveTransport

/-!
# The source integral on the selected P(dN) carrier

The p dividing d deletion is separate from the p dividing N deletion.
The two written shifted arguments agree on the actual prime fibres;
no false global identity at p = 0 or p = 1 is used.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem reboxingPrimeSum_log_parameter_eq {i k N : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (selected : Bool) (f : ℝ → ℝ)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    reboxingPrimeSum selected N δ s t (convolutionWuWindows N Δ V)
        (fun d p => f (log (((N : ℝ) ^ (1 / 2 - δ) / d) / p) / log p)) =
      reboxingPrimeSum selected N δ s t (convolutionWuWindows N Δ V)
        (fun d p => f (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)) := by
  unfold reboxingPrimeSum
  congr 1
  apply sum_congr rfl
  intro d hd
  congr 1
  apply sum_congr rfl
  intro p hp
  have hq := (wu_buchstab_prime_window_bounds hN hδ hδhi hb hs hst ht hd).2.2.1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_primeWindow.mp hp).1.one_lt
  dsimp only
  rw [log_div (by linarith : (N : ℝ) ^ (1 / 2 - δ) / d ≠ 0)
    (by linarith : (p : ℝ) ≠ 0), sub_div, div_self (log_pos hp1).ne']

theorem wu_effective_shifted_prime_transport_relative (upper : Bool) (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let g := fun d p : ℕ => wuEffectiveCoefficient upper (k + 1) δ N0
          (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)
        |reboxingPrimeSum false N δ s t W g - reboxingPrimeSum true N δ s t W g| ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  obtain ⟨T, hT4, hT⟩ := wu_effective_prime_transport_relative upper k hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N0 hN0 N hN i Δ V hb s t hs hst ht
  have h := hT N0 hN0 N hN i Δ V hb s t hs hst ht
  dsimp only at h ⊢
  rw [reboxingPrimeSum_log_parameter_eq false _ (by omega) hδ hδhi hb hs hst ht,
    reboxingPrimeSum_log_parameter_eq true _ (by omega) hδ hδhi hb hs hst ht] at h
  exact h

theorem wu_reboxing_selected_prime_integral_relative (upper : Bool) (k : ℕ)
    {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      |reboxingPrimeSum true N δ s t (convolutionWuWindows N Δ V)
          (fun d p => wuEffectiveCoefficient upper (k + 1) δ N0
            (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)) -
        (∫ u in (s - 1)..(t - 1), wuEffectiveCoefficient upper (k + 1) δ N0 u / u) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)| ≤
      ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT14, hT1⟩ :=
    wu_reboxing_prime_integral_relative upper k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hT2⟩ :=
    wu_effective_shifted_prime_transport_relative upper k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN i Δ V hb s t hs hst ht
  have h1 := hT1 N0 ((le_max_left _ _).trans hN0) N hN i Δ V hb s t hs hst ht
  have h2 := hT2 N0 ((le_max_right _ _).trans hN0) N hN i Δ V hb s t hs hst ht
  dsimp only at h2
  rw [abs_sub_comm] at h2
  exact (abs_sub_le _ _ _).trans ((add_le_add h2 h1).trans_eq (by ring))

end Wu2008DoubleSieve
