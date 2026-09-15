import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprimeEuler

/-!
# Uniform relative payment of the actual non-coprime switched error

All constants and thresholds precede the source boxes, the two cutoffs,
and the finite admissible set of squarefree sieve moduli.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem omega3_absolute_power_log_relative (k m : ℕ) {δ ε C ρ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε)
    (hC : 0 < C) (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        C * N * log N ^ m / (N : ℝ) ^ ρ ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨c, hc, T1, hT1⟩ := wu_boxTheta_lower k hδ hδhi
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget (m + (5 * k + 2))
      (show 0 < C / (ε * c) by positivity) hρ)
  refine ⟨max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N hN i Δ V hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have htheta := hT1 N hN1 i hb.1 Δ hb.2.1 hb.2.2.1 V hb.2.2.2.2.1 hb.2.2.2.2.2
  calc
    _ ≤ C * N * log N ^ m /
        ((C / (ε * c)) * log N ^ (m + (5 * k + 2))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (hT2 N hN2)
    _ = ε * (c * (N : ℝ) / log N ^ (5 * k + 2)) := by
      rw [pow_add]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta hε.le

theorem omega3_non_coprime_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ z : ℝ, z ≤ N → ∀ M : Finset ℕ,
      M ⊆ (ordinarySievePrimeProduct N z).divisors → (∀ q ∈ M, q ≤ N) →
      let W := convolutionWuWindows N Δ V
      (∑ q ∈ M, ((3 : ℝ) ^ q.primeFactors.card / Nat.totient q) *
        ∑ c ∈ (omega3CofactorLabels N δ s t W).filter
          (fun c => ¬ (omega3CofactorValue c).Coprime q),
          (convolutionCoeff W c.1 : ℝ) * (omega3CofactorPrimeFibreLE N δ s c).card) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  let η := wuLocalExponent k δ / 10
  let B := (max 1 (1 / η)) ^ (k + 2)
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hB : 0 < B := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  obtain ⟨C, hC, hbound⟩ := omega3_non_coprime_euler_bound
  obtain ⟨T1, hT14, hT1⟩ := omega3_cofactor_labels_geometry k hδ hδhi
  obtain ⟨T2, _, hT2⟩ := omega3_cofactor_labels_fibre_uniform k hδ hδhi
  obtain ⟨T3, _, hT3⟩ := omega3_absolute_power_log_relative k 5 hδ hδhi hε
    (show 0 < 2 * C * B / log 2 by positivity) hη
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T4, hT4⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T1 (max T2 (max T3 T4)), hT14.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb s t hs hst ht z hz M hM hqN
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_left T3 _).trans
    ((le_max_right T2 _).trans ((le_max_right T1 _).trans hN))
  have hN4 := (le_max_right T3 _).trans
    ((le_max_right T2 _).trans ((le_max_right T1 _).trans hN))
  have hN4' : 4 ≤ N := hT14.trans hN1
  have hlog1 := hT4 N hN4
  have hY : 0 < (N : ℝ) ^ η := rpow_pos_of_pos (by positivity) _
  have hgeom := hT1 N hN1 i Δ V hb s t hs hst ht
  have hfibre := hT2 N hN2 i Δ V hb s t hs hst ht
  have h := hbound N (by omega) i δ s t z ((N : ℝ) ^ η) B
    (convolutionWuWindows N Δ V) M hz hY hB.le hM hqN
    (fun c hc => ⟨(hgeom c hc).1, (hgeom c hc).2.2.1, (hgeom c hc).2.2.2.2⟩)
    hfibre
  dsimp only
  calc
    _ ≤ C * B * N * ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ η * log 2)) := h
    _ ≤ C * B * N * ((2 * log N) * log N ^ 4 / ((N : ℝ) ^ η * log 2)) := by
      gcongr
      linarith
    _ = (2 * C * B / log 2) * N * log N ^ 5 / (N : ℝ) ^ η := by ring
    _ ≤ _ := hT3 N hN3 i Δ V hb

end Wu2008DoubleSieve
