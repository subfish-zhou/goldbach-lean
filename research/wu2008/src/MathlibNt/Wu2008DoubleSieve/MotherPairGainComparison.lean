import MathlibNt.Wu2008DoubleSieve.MotherPairGainData
import MathlibNt.Wu2008DoubleSieve.Gamma78GainCell

namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- General fixed cutoff comparison; the mother parameter is not specialized. -/
theorem fixed_cutoff_le {R p q S s : ℝ} (hR : 1 < R) (hp : 0 < p)
    (hq : 0 < q) (hS : 0 < S) (hs : 0 < s)
    (hv : S * (1 - log p / log R - log q / log R) ≤ s) :
    (R / (p*q))^(1/s) ≤ R^(1/S) := by
  have hR0 : 0 < R := by linarith
  have hL : 0 < R/(p*q) := div_pos hR0 (mul_pos hp hq)
  have hr : log (R/(p*q)) = log R * (1-log p/log R-log q/log R) := by
    rw [log_div hR0.ne' (mul_pos hp hq).ne', log_mul hp.ne' hq.ne']
    field_simp [(log_pos hR).ne']
    ring
  apply (log_le_log_iff (rpow_pos_of_pos hL _) (rpow_pos_of_pos hR0 _)).mp
  rw [log_rpow hL, log_rpow hR0, hr]
  have hh := mul_le_mul_of_nonneg_left hv (log_pos hR).le
  apply (le_of_mul_le_mul_left ?_ (mul_pos hs hS))
  field_simp at *
  nlinarith

/-- Uniform physical dictionary for the complete original labels. -/
theorem termLabels_eq_rect {i : ℕ} (p : SecondFunctionalParameters) (j : Term)
    (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    termLabels p j N δ W = rectLabels N δ W (1/p.S) (upperP p j)
      (lowerQ p j) (upperQ p j) := by
  cases j <;> rfl

noncomputable def termCutoff (p : SecondFunctionalParameters) (j : Term)
    (N : ℕ) (δ : ℝ) (x : Gamma5ClassicalLabel) : ℝ :=
  match j with
  | .gammaFive | .gammaSix => wuLocalCutoff N δ x.1 p.S
  | .gammaSeven | .gammaEight => x.2.1

theorem termCount_eq_sum {i : ℕ} (p : SecondFunctionalParameters) (j : Term)
    (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) (X : Finset Gamma5ClassicalLabel) :
    termCount p j N δ W X = ∑ x ∈ X, (convolutionCoeff W x.1 : ℝ) *
      (sourceSieveCount N (gamma5ClassicalProduct x) (x.1*N)
        (termCutoff p j N δ x) : ℝ) := by
  cases j <;> rfl

theorem term_cutoff_le_selected {i : ℕ} (p : SecondFunctionalParameters) (j : Term)
    (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) {x : Gamma5ClassicalLabel}
    (hx : x ∈ termLabels p j N δ W) : termCutoff p j N δ x ≤ x.2.1 := by
  rw [termLabels_eq_rect] at hx
  have h := (mem_filter.mp hx).2.2.2.2.2.1
  cases j with
  | gammaFive => exact h
  | gammaSix => exact h
  | gammaSeven => exact le_rfl
  | gammaEight => exact le_rfl

theorem term_cutoff_comparison (p : SecondFunctionalParameters) (h : AnalyticParameters p)
    (j : Term) {N : ℕ} {δ s : ℝ} {x : Gamma5ClassicalLabel}
    (hR : 1 < (N:ℝ)^(1/2-δ)/x.1) (hp : x.2.1.Prime) (hq : x.2.2.Prime)
    (hs : 0 < s)
    (hv : Hratio p j (gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.1)
      (gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.2) ≤ s) :
    wuLocalCutoff N δ (gamma5ClassicalProduct x) s ≤ termCutoff p j N δ x := by
  have he : ((N:ℝ)^(1/2-δ)/x.1) / ((x.2.1:ℝ)*x.2.2) =
      (N:ℝ)^(1/2-δ)/gamma5ClassicalProduct x := by
    simp only [gamma5ClassicalProduct, Nat.cast_mul]
    ring
  have hf := fixed_cutoff_le (p := (x.2.1:ℝ)) (q := (x.2.2:ℝ)) hR (by exact_mod_cast hp.pos)
    (by exact_mod_cast hq.pos) (by linarith [h.three_le_S] : 0 < p.S) hs
  have hvv := gamma78Gain_cutoff_le (p := (x.2.1:ℝ)) (q := (x.2.2:ℝ)) hR (by exact_mod_cast hp.one_lt)
    (by exact_mod_cast hq.pos) hs
  cases j with
  | gammaFive => simpa only [termCutoff, wuLocalCutoff, he] using hf hv
  | gammaSix => simpa only [termCutoff, wuLocalCutoff, he] using hf hv
  | gammaSeven => simpa only [termCutoff, wuLocalCutoff, he] using hvv hv
  | gammaEight => simpa only [termCutoff, wuLocalCutoff, he] using hvv hv

/-- Complete convolution multiplicities and the actual source mask are retained. -/
theorem cell_count_le_phi (p : SecondFunctionalParameters) (h : AnalyticParameters p)
    (j : Term) {i k N : ℕ} {δ Δ P Q s : ℝ}
    {V : Fin i → ℝ} {U : Fin (i+2) → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 0 < s)
    (hsub : gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
      termLabels p j N δ (convolutionWuWindows N Δ V))
    (hv : ∀ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
      Hratio p j (gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.1)
        (gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.2) ≤ s)
    (hU : ∀ F : ℕ → ℝ,
      (∑ m ∈ boxConvolutionSupport (convolutionWuWindows N Δ U),
        (convolutionCoeff (convolutionWuWindows N Δ U) m : ℝ)*F m) =
      ∑ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ)*F (gamma5ClassicalProduct x)) :
    termCount p j N δ (convolutionWuWindows N Δ V)
      (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) ≤
      wuBoxPhi N δ (convolutionWuWindows N Δ U) s := by
  rw [termCount_eq_sum]
  change _ ≤ ∑ m ∈ boxConvolutionSupport (convolutionWuWindows N Δ U),
    (convolutionCoeff (convolutionWuWindows N Δ U) m : ℝ) *
      (sourceSieveCount N m (m*N) (wuLocalCutoff N δ m s) : ℝ)
  rw [hU]
  apply sum_le_sum
  intro x hx
  have hxl := hsub hx
  rw [termLabels_eq_rect] at hxl
  obtain ⟨hmem,hp,hq,_hpN,_hqN,_hpa,_hpb,_hqa,_hqb,hpq⟩ := mem_filter.mp hxl
  have hd := (mem_product.mp hmem).1
  have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
  have hc := term_cutoff_comparison p h j hR hp hq hs (hv x hx)
  have hz := term_cutoff_le_selected p j N δ _ (hsub hx)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  change (sourceSieveCount N (x.1*x.2.1*x.2.2) (x.1*N) _ : ℝ) ≤ _
  rw [gamma5Classical_source_count_eq hp hq hz (hz.trans (by exact_mod_cast hpq.le))]
  exact gamma5Classical_source_count_antitone _ _ _ hc

/-- Conditional internal comparison; rectangle admission is supplied separately. -/
theorem gain_grid_comparison (p : SecondFunctionalParameters) (h : AnalyticParameters p)
    (j : Term) (k : ℕ) {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hη : 0 < η)
    (s : ℝ) (hs : s ∈ Icc (1:ℝ) 3) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ P Q : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      ((N:ℝ)^(1/2-δ)/(∏ a, V a))^(1/10:ℝ) ≤ Q →
      Q ≤ ((N:ℝ)^(1/2-δ)/(∏ a, V a))^(1/2:ℝ) →
      ((N:ℝ)^(1/2-δ)/((∏ a, V a)*Q))^(1/10:ℝ) ≤ P →
      P ≤ ((N:ℝ)^(1/2-δ)/((∏ a, V a)*Q))^(1/2:ℝ) →
      gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
        termLabels p j N δ (convolutionWuWindows N Δ V) →
      (∀ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        Hratio p j (gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.1)
          (gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.2) ≤ s) →
      termCount p j N δ (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) ≤
      (1-wuImprovementLimit true δ s+η)*gamma5ClassicalMainMass N δ
        (convolutionWuWindows N Δ V) (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) := by
  obtain ⟨T,hT⟩ := wuImprovementLimit_sub_mem true (k+1) hδ (by linarith)
    hs.1 (by linarith [hs.2]) hη
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN he i Δ P Q V hb hQlo hQhi hPlo hPhi hsub hv
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨U,hUbox,hU⟩ := gamma5Gain_sorted_two (by omega) hδ hδhi hb hQlo hQhi hPlo hPhi
  have hc := hT N ((le_max_right _ _).trans hN) hN4 he (i+2) Δ U hUbox
  change wuBoxPhi N δ (convolutionWuWindows N Δ U) s ≤
    (wuUpperCoefficient s-(wuImprovementLimit true δ s-η))*_ at hc
  rw [show wuUpperCoefficient s = 1 from jr1965F_normalized_initial
    (by linarith [hs.1]) hs.2, gamma5Gain_cell_theta hU] at hc
  have hp := cell_count_le_phi p h j (by omega) hδ (by linarith) hb
    (by linarith [hs.1]) hsub hv hU
  convert hp.trans hc using 1 <;> first | rfl | ring

end Wu2008DoubleSieve.MotherPair
