import MathlibNt.Wu2008DoubleSieve.Gamma5GainKernel
import MathlibNt.Wu2008DoubleSieve.Gamma5MassMain
import MathlibNt.Wu2008DoubleSieve.ReboxingSorted

/-!
# Real sorted two-insertion cells and their upper comparison

Every cell keeps the entire original convolution box. Its mass is exactly
the new sorted box Theta, with no change to convolution multiplicity.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

noncomputable def gamma5GainCell {i : ℕ} (N : ℕ) (Δ P Q : ℝ)
    (W : Fin i → Finset ℕ) : Finset Gamma5ClassicalLabel :=
  boxConvolutionSupport W ×ˢ (primeWindow N (P / Δ) P ×ˢ primeWindow N (Q / Δ) Q)

theorem gamma5Gain_double_sum {i : ℕ} (W : Fin i → Finset ℕ) (P Q : Finset ℕ)
    (F : ℕ → ℝ) :
    (∑ m ∈ boxConvolutionSupport (Fin.cons P (Fin.cons Q W)),
      (convolutionCoeff (Fin.cons P (Fin.cons Q W)) m : ℝ) * F m) =
    ∑ x ∈ boxConvolutionSupport W ×ˢ (P ×ˢ Q),
      (convolutionCoeff W x.1 : ℝ) * F (gamma5ClassicalProduct x) := by
  rw [boxConvolution_sum_cons P (Fin.cons Q W),
    boxConvolution_sum_cons Q W, sum_product]
  apply sum_congr rfl
  intro d _
  rw [sum_product]
  simp only [mul_sum, gamma5ClassicalProduct]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  rw [show d * q * p = d * p * q by ring]

theorem gamma5Gain_sorted_two {i k N : ℕ} {δ Δ P Q : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hb : wuSourceBox k δ N i Δ V)
    (hQlo : ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / 10 : ℝ) ≤ Q)
    (hQhi : Q ≤ ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / 2 : ℝ))
    (hPlo : ((N : ℝ) ^ (1 / 2 - δ) / ((∏ j, V j) * Q)) ^ (1 / 10 : ℝ) ≤ P)
    (hPhi : P ≤ ((N : ℝ) ^ (1 / 2 - δ) / ((∏ j, V j) * Q)) ^ (1 / 2 : ℝ)) :
    ∃ U : Fin (i + 2) → ℝ,
      wuSourceBox (k + 2) δ N (i + 2) Δ U ∧
      ∀ F : ℕ → ℝ,
        (∑ m ∈ boxConvolutionSupport (convolutionWuWindows N Δ U),
          (convolutionCoeff (convolutionWuWindows N Δ U) m : ℝ) * F m) =
        ∑ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
          (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
            F (gamma5ClassicalProduct x) := by
  obtain ⟨e, he, _⟩ := wuSourceBox_sorted_insertion_convolution hN hδ hδhi hb
    (by norm_num : (2 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 10) le_rfl hQlo hQhi
  have hp : (∏ j, (Fin.cons Q V ∘ e) j) = (∏ j, V j) * Q := by
    simp only [Function.comp_apply]
    rw [Equiv.prod_comp, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_comm]
  obtain ⟨f, hf, _⟩ := wuSourceBox_sorted_insertion_convolution (α := P) hN hδ hδhi he
    (by norm_num : (2 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 10) le_rfl
    (by rw [hp]; exact hPlo) (by rw [hp]; exact hPhi)
  refine ⟨Fin.cons P (Fin.cons Q V ∘ e) ∘ f, hf, ?_⟩
  intro F
  simp only [convolutionWuWindows_permute, convolutionWuWindows_cons,
    boxConvolutionSupport_permute, convolutionCoeff_permute]
  rw [boxConvolution_sum_cons]
  simp only [boxConvolutionSupport_permute, convolutionCoeff_permute]
  rw [← boxConvolution_sum_cons]
  exact gamma5Gain_double_sum _ _ _ _

theorem gamma5Gain_cutoff_le {R p q s : ℝ} (hR : 1 < R) (hp : 0 < p) (hq : 0 < q)
    (hs : 0 < s)
    (hv : gamma5GainV (log p / log R) (log q / log R) ≤ s) :
    (R / (p * q)) ^ (1 / s) ≤ R ^ (1 / gamma5ClassicalS) := by
  have hR0 := lt_trans (by norm_num : (0 : ℝ) < 1) hR
  have hL : 0 < R / (p * q) := div_pos hR0 (mul_pos hp hq)
  have hz : 0 < log (R ^ (1 / gamma5ClassicalS)) :=
    log_pos (one_lt_rpow hR (by norm_num [gamma5ClassicalS]))
  have hr := gamma5Classical_ratio_coordinates hR hp hq
  have hv' : log (R / (p * q)) / log (R ^ (1 / gamma5ClassicalS)) ≤ s := by
    rw [hr]
    exact hv
  have hh := (div_le_iff₀ hz).mp hv'
  apply (log_le_log_iff (rpow_pos_of_pos hL _) (rpow_pos_of_pos hR0 _)).mp
  rw [log_rpow hL]
  rw [one_div_mul_eq_div, div_le_iff₀ hs]
  simpa only [mul_comm] using hh

theorem gamma5Gain_cell_count_le_phi {i k N : ℕ} {δ Δ P Q s : ℝ}
    {V : Fin i → ℝ} {U : Fin (i + 2) → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 0 < s)
    (hsub : gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
      gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V))
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
  unfold wuBoxPhi convolutionSieveCount
  rw [hU]
  apply sum_le_sum
  intro x hx
  obtain ⟨hd, hp, hq, _hpN, _hqN, hz, hpq, _hqu⟩ :=
    (gamma5Classical_mem_labels_iff hN hδ hδhi hb x).mp (hsub hx)
  have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
  have hc := gamma5Gain_cutoff_le hR (by exact_mod_cast hp.pos)
    (by exact_mod_cast hq.pos) hs (hv x hx)
  have he : ((N : ℝ) ^ (1 / 2 - δ) / x.1) / ((x.2.1 : ℝ) * x.2.2) =
      (N : ℝ) ^ (1 / 2 - δ) / gamma5ClassicalProduct x := by
    simp only [gamma5ClassicalProduct, Nat.cast_mul]
    ring
  rw [he] at hc
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  change (sourceSieveCount N (x.1 * x.2.1 * x.2.2) (x.1 * N) _ : ℝ) ≤ _
  rw [gamma5Classical_source_count_eq hp hq hz (hz.trans (by exact_mod_cast hpq.le))]
  exact gamma5Classical_source_count_antitone _ _ _ hc

theorem gamma5Gain_cell_theta {i N : ℕ} {δ Δ P Q : ℝ}
    {V : Fin i → ℝ} {U : Fin (i + 2) → ℝ}
    (hU : ∀ F : ℕ → ℝ,
      (∑ m ∈ boxConvolutionSupport (convolutionWuWindows N Δ U),
        (convolutionCoeff (convolutionWuWindows N Δ U) m : ℝ) * F m) =
      ∑ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) * F (gamma5ClassicalProduct x)) :
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U) =
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) := by
  unfold boxTheta gamma5ClassicalMainMass
  simp only [mul_div_assoc]
  rw [hU]

/-- A single threshold for the predetermined finite right-endpoint grid.
The eventual family consumed is the real depth k+2 family. -/
theorem gamma5Gain_grid_comparison (k : ℕ) {δ η : ℝ}
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
        gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V) →
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
  have hp := gamma5Gain_cell_count_le_phi (by omega) hδ (by linarith) hb
    (by linarith [(hJ s hs).1]) hsub hv hU
  convert hp.trans hc using 1 <;> first | rfl | ring

end Wu2008DoubleSieve
