import MathlibNt.Wu2008DoubleSieve.Gamma6GainGeometry

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem gamma6Gain_cell_count_le_phi {i k N : ℕ} {δ Δ P Q s : ℝ}
    {V : Fin i → ℝ} {U : Fin (i + 2) → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 0 < s)
    (hsub : gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
      gamma6BaseLabels N δ (convolutionWuWindows N Δ V))
    (hv : ∀ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
      gamma5GainV
        (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
        (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ s)
    (hU : ∀ F : ℕ → ℝ,
      (∑ m ∈ boxConvolutionSupport (convolutionWuWindows N Δ U),
        (convolutionCoeff (convolutionWuWindows N Δ U) m : ℝ) * F m) =
      ∑ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) * F (gamma5ClassicalProduct x)) :
    gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
      (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) ≤
      wuBoxPhi N δ (convolutionWuWindows N Δ U) s := by
  change _ ≤ ∑ m ∈ boxConvolutionSupport (convolutionWuWindows N Δ U),
    (convolutionCoeff (convolutionWuWindows N Δ U) m : ℝ) *
      (sourceSieveCount N m (m * N) (wuLocalCutoff N δ m s) : ℝ)
  rw [hU]
  apply sum_le_sum
  intro x hx
  obtain ⟨hd, hp, hq, _hpN, _hqN, hz, hpu, hql, _hqu⟩ :=
    (gamma6Base_mem_labels_iff hN hδ hδhi hb x).mp (hsub hx)
  have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
  have hpq : (x.2.1 : ℝ) < x.2.2 := gamma6Base_prime_order hR hpu hql
  have hc := gamma5Gain_cutoff_le hR (by exact_mod_cast hp.pos)
    (by exact_mod_cast hq.pos) hs (hv x hx)
  have he : ((N : ℝ) ^ (1 / 2 - δ) / x.1) / ((x.2.1 : ℝ) * x.2.2) =
      (N : ℝ) ^ (1 / 2 - δ) / gamma5ClassicalProduct x := by
    simp only [gamma5ClassicalProduct, Nat.cast_mul]
    ring
  rw [he] at hc
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  change (sourceSieveCount N (x.1 * x.2.1 * x.2.2) (x.1 * N) _ : ℝ) ≤ _
  rw [gamma5Classical_source_count_eq hp hq hz (hz.trans hpq.le)]
  exact gamma5Classical_source_count_antitone _ _ _ hc

theorem gamma6Gain_grid_comparison (k : ℕ) {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hη : 0 < η)
    (J : Finset ℝ) (hJ : ∀ s ∈ J, s ∈ Icc (1 : ℝ) 3) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ s ∈ J, ∀ i : ℕ, ∀ Δ P Q : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / 10 : ℝ) ≤ Q →
      Q ≤ ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / 2 : ℝ) →
      ((N : ℝ) ^ (1 / 2 - δ) / ((∏ j, V j) * Q)) ^ (1 / 10 : ℝ) ≤ P →
      P ≤ ((N : ℝ) ^ (1 / 2 - δ) / ((∏ j, V j) * Q)) ^ (1 / 2 : ℝ) →
      gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
        gamma6BaseLabels N δ (convolutionWuWindows N Δ V) →
      (∀ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        gamma5GainV
          (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
          (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ s) →
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) ≤
      (1 - wuImprovementLimit true δ s + η) *
        gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) := by
  have hmem (s : ℝ) (hs : s ∈ J) :
      ∀ᶠ N : ℕ in atTop, wuImprovementLimit true δ s - η ∈
        wuAdmissibleImprovements true (k + 2) δ s N := by
    obtain ⟨T, hT⟩ := wuImprovementLimit_sub_mem true (k + 1) hδ (by linarith)
      (hJ s hs).1 (by linarith [(hJ s hs).2]) hη
    exact (eventually_ge_atTop T).mono (fun _ hN =>
      wuAdmissibleImprovements_mono_threshold true _ _ _ hN hT)
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((eventually_all_finset J).mpr hmem)
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN he s hs i Δ P Q V hb hQlo hQhi hPlo hPhi hsub hv
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨U, hUbox, hU⟩ := gamma5Gain_sorted_two (by omega) hδ hδhi hb hQlo hQhi hPlo hPhi
  have hc := hT N ((le_max_right _ _).trans hN) s hs N le_rfl hN4 he (i + 2) Δ U hUbox
  change wuBoxPhi N δ (convolutionWuWindows N Δ U) s ≤
    (wuUpperCoefficient s - (wuImprovementLimit true δ s - η)) * _ at hc
  rw [show wuUpperCoefficient s = 1 from
    jr1965F_normalized_initial (by linarith [(hJ s hs).1]) (hJ s hs).2,
    gamma5Gain_cell_theta hU] at hc
  have hp := gamma6Gain_cell_count_le_phi (by omega) hδ (by linarith) hb
    (by linarith [(hJ s hs).1]) hsub hv hU
  convert hp.trans hc using 1 <;> first | rfl | ring

end Wu2008DoubleSieve
