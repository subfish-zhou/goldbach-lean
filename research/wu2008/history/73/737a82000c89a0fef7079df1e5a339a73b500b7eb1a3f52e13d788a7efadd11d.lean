import R2Gamma5FullMass
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairClassicalSource

noncomputable section

namespace WuPaper.R2Gamma5

open Finset Set Real Wu2008DoubleSieve Wu2008DoubleSieve.MotherPair
open scoped Classical

theorem fixed_cutoff_eq {R P Q S : ℝ}
    (hR : 1 < R) (hP : 0 < P) (hQ : 0 < Q) (hS : 0 < S)
    (hr : 0 < S * (1 - log P / log R - log Q / log R)) :
    (R / (P * Q)) ^ (1 / (S * (1 - log P / log R - log Q / log R))) =
      R ^ (1 / S) := by
  have hR0 : 0 < R := by linarith
  have hlR : log R ≠ 0 := (log_pos hR).ne'
  have hb : 1 - log P / log R - log Q / log R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hr
    exact (lt_irrefl 0) hr
  have he : log (R / (P * Q)) =
      log R * (1 - log P / log R - log Q / log R) := by
    rw [log_div hR0.ne' (mul_pos hP hQ).ne', log_mul hP.ne' hQ.ne']
    field_simp
    ring
  rw [rpow_def_of_pos (div_pos hR0 (mul_pos hP hQ)), rpow_def_of_pos hR0, he]
  congr 1
  field_simp

theorem full_label_cutoff_eq {p : SecondFunctionalParameters} (hp : FullParameters p)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) {x : Gamma5ClassicalLabel}
    (hx : x ∈ termLabels p .gammaFive N δ (convolutionWuWindows N Δ V)) :
    wuLocalCutoff N δ (gamma5ClassicalProduct x) (localRatio p N δ x) =
      wuLocalCutoff N δ x.1 p.S := by
  have hr := full_label_ratio_mem hp hN hδ hδhi hb hx
  obtain ⟨hm, hP, hQ, _, _, _, _, _, _, _⟩ := mem_filter.mp hx
  have hR := (gamma5Mass_support_geometry hN hδ hδhi hb
    (mem_product.mp hm).1).2.2.1
  have he : ((N : ℝ) ^ (1 / 2 - δ) / x.1) /
      ((x.2.1 : ℝ) * x.2.2) =
      (N : ℝ) ^ (1 / 2 - δ) / gamma5ClassicalProduct x := by
    simp only [gamma5ClassicalProduct, Nat.cast_mul]
    ring
  have hc := fixed_cutoff_eq hR (by exact_mod_cast hP.pos)
    (by exact_mod_cast hQ.pos) (by linarith [hp.three_le_S] : 0 < p.S)
    (show 0 < localRatio p N δ x by linarith [hr.1])
  simpa only [he, wuLocalCutoff, localRatio, gamma5MassCoordinate] using hc

theorem full_count_exact_phi_atoms {p : SecondFunctionalParameters}
    (hp : FullParameters p) {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 5 =
      ∑ x ∈ termLabels p .gammaFive N δ (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          (sourceSieveCount N (gamma5ClassicalProduct x) (gamma5ClassicalProduct x * N)
            (wuLocalCutoff N δ (gamma5ClassicalProduct x) (localRatio p N δ x)) : ℝ) := by
  rw [← termCount_eq_original p hp.toAnalyticParameters .gammaFive hN hδ hδhi hb,
    termCount_eq_sum]
  apply sum_congr rfl
  intro x hx
  rw [full_label_cutoff_eq hp hN hδ hδhi hb hx]
  obtain ⟨_, hP, hQ, _, _, _, _, _, _, hPQ⟩ := mem_filter.mp hx
  have hz := term_cutoff_le_selected p .gammaFive N δ _ hx
  dsimp only [termCutoff] at hz ⊢
  congr 2
  exact gamma5Classical_source_count_eq hP hQ hz
    (hz.trans (by exact_mod_cast hPQ.le))

def rawEndpoints {i : ℕ} (P Q : ℝ) (V : Fin i → ℝ) : Fin (i + 2) → ℝ :=
  Fin.cons P (Fin.cons Q V)

theorem raw_cell_convolution {i : ℕ} (N : ℕ) (Δ P Q : ℝ)
    (V : Fin i → ℝ) (F : ℕ → ℝ) :
    (∑ m ∈ boxConvolutionSupport (convolutionWuWindows N Δ (rawEndpoints P Q V)),
      (convolutionCoeff (convolutionWuWindows N Δ (rawEndpoints P Q V)) m : ℝ) * F m) =
      ∑ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          F (gamma5ClassicalProduct x) := by
  simp only [rawEndpoints, convolutionWuWindows_cons]
  exact gamma5Gain_double_sum _ _ _ _

theorem raw_cell_theta {i : ℕ} (N : ℕ) (δ Δ P Q : ℝ) (V : Fin i → ℝ) :
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
        (convolutionWuWindows N Δ (rawEndpoints P Q V)) =
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) := by
  exact gamma5Gain_cell_theta (raw_cell_convolution N Δ P Q V)

theorem full_cell_count_le_raw_phi (p : SecondFunctionalParameters)
    (hp : AnalyticParameters p) {i k N : ℕ} {δ Δ P Q s : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 0 < s)
    (hsub : gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
      termLabels p .gammaFive N δ (convolutionWuWindows N Δ V))
    (hr : ∀ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
      localRatio p N δ x ≤ s) :
    termCount p .gammaFive N δ (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) ≤
      wuBoxPhi N δ (convolutionWuWindows N Δ (rawEndpoints P Q V)) s := by
  exact cell_count_le_phi p hp .gammaFive hN hδ hδhi hb hs hsub hr
    (raw_cell_convolution N Δ P Q V)

theorem two_endpoint_prefixes {R P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) :
    boxSquaredPrefixes R (![Q, P] : Fin 2 → ℝ) ↔ Q ^ 2 ≤ R ∧ Q * P ^ 2 ≤ R := by
  rw [boxSquaredPrefixes_cons_iff hQ, boxSquaredPrefixes_cons_iff hP]
  have hz (L : ℝ) : boxSquaredPrefixes L (![] : Fin 0 → ℝ) := by
    intro j
    exact Fin.elim0 j
  simp only [hz, and_true, le_div_iff₀ hQ]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by nlinarith only [h2]⟩

theorem two_endpoint_prefixes_iff_legal {R t u : ℝ} (hR : 1 < R) :
    boxSquaredPrefixes R (![R ^ u, R ^ t] : Fin 2 → ℝ) ↔
      gamma5GainLegal t u := by
  have hR0 : 0 < R := by linarith
  rw [two_endpoint_prefixes (rpow_pos_of_pos hR0 _) (rpow_pos_of_pos hR0 _)]
  have hpow (v : ℝ) : (R ^ v) ^ 2 = R ^ (2 * v) := by
    rw [← rpow_natCast_mul hR0.le]
    congr 1
    ring
  rw [hpow, hpow, ← rpow_add hR0]
  have hc (v : ℝ) : R ^ v ≤ R ↔ v ≤ 1 := by
    conv_lhs => rhs; rw [← rpow_one R]
    exact rpow_le_rpow_left_iff hR
  rw [hc, hc]
  rfl

theorem unit_pair_not_sourceBox {N k : ℕ} {δ Δ t u : ℝ}
    (hR : 1 < (N : ℝ) ^ (1 / 2 - δ)) (hbad : 1 < u + 2 * t) :
    ¬ wuSourceBox k δ N 2 Δ
      (![((N : ℝ) ^ (1 / 2 - δ)) ^ u,
         ((N : ℝ) ^ (1 / 2 - δ)) ^ t] : Fin 2 → ℝ) := by
  intro hb
  have h := (two_endpoint_prefixes_iff_legal hR).mp hb.2.2.2.2.2
  exact (not_lt_of_ge h.2) hbad

#check @WuPaper.R2Gamma5.fixed_cutoff_eq
#print axioms WuPaper.R2Gamma5.fixed_cutoff_eq
#check @WuPaper.R2Gamma5.full_label_cutoff_eq
#print axioms WuPaper.R2Gamma5.full_label_cutoff_eq
#check @WuPaper.R2Gamma5.full_count_exact_phi_atoms
#print axioms WuPaper.R2Gamma5.full_count_exact_phi_atoms
#check @WuPaper.R2Gamma5.rawEndpoints
#print axioms WuPaper.R2Gamma5.rawEndpoints
#check @WuPaper.R2Gamma5.raw_cell_convolution
#print axioms WuPaper.R2Gamma5.raw_cell_convolution
#check @WuPaper.R2Gamma5.raw_cell_theta
#print axioms WuPaper.R2Gamma5.raw_cell_theta
#check @WuPaper.R2Gamma5.full_cell_count_le_raw_phi
#print axioms WuPaper.R2Gamma5.full_cell_count_le_raw_phi
#check @WuPaper.R2Gamma5.two_endpoint_prefixes
#print axioms WuPaper.R2Gamma5.two_endpoint_prefixes
#check @WuPaper.R2Gamma5.two_endpoint_prefixes_iff_legal
#print axioms WuPaper.R2Gamma5.two_endpoint_prefixes_iff_legal
#check @WuPaper.R2Gamma5.unit_pair_not_sourceBox
#print axioms WuPaper.R2Gamma5.unit_pair_not_sourceBox

end WuPaper.R2Gamma5
