import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedFamily
import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateDistribution

/-! # Fixed full-profile layers, gated signed residuals and noncoprime mass -/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

noncomputable def fourthRowTripleGatedLayerCoefficient {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (ten : Bool) (j e : ℕ) : ℝ :=
  let L := omega3CofactorLabels N δ (5 / 2) (103 / 25) W
  let c := omega3LayerLabel L j e
  if fourthRowTripleGatedBand N δ ten c.1 c.2.2.1 c.2.1
    then omega3LayerCoefficient W L j e else 0

theorem fourthRowTripleGated_R1_layers {i N D B : ℕ} {δ Z : ℝ}
    (W : Fin i → Finset ℕ) (ten : Bool)
    (hB : ∀ e, (omega3LayerFibre (omega3CofactorLabels N δ (5 / 2) (103 / 25) W) e).card ≤ B)
    (hg : ∀ c ∈ omega3CofactorLabels N δ (5 / 2) (103 / 25) W,
      0 < omega3CofactorValue c ∧ 0 < wuLocalCutoff N δ c.1 (291 / 100)) :
    let L := omega3CofactorLabels N δ (5 / 2) (103 / 25) W
    fourthRowTripleGatedR1 N D δ Z W (fourthRowTripleGatedProfiles N δ W ten) ≤
      ∑ j ∈ range B, ∑ q ∈ omega3SieveModuli N D Z, (3 : ℝ) ^ q.primeFactors.card *
        |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
          fourthRowTripleGatedLayerCoefficient N δ W ten j e *
            omega3ProfileError N q e
              (fourthRowTripleGatedLower N δ (omega3LayerLabel L j e))
              (fourthRowTripleGatedUpper N δ (omega3LayerLabel L j e))| := by
  intro L
  have h := omega3Layer_modulus_sum_le W L B hB (omega3SieveModuli N D Z)
    (fun q => (3 : ℝ) ^ q.primeFactors.card) (fun _ _ => by positivity)
    (fun q c => if fourthRowTripleGatedBand N δ ten c.1 c.2.2.1 c.2.1 then
      (fourthRowTripleGatedAP N δ c q : ℝ) -
        (fourthRowTripleGatedFibre N δ c).card / (Nat.totient q : ℝ) else 0)
  have hl : fourthRowTripleGatedR1 N D δ Z W (fourthRowTripleGatedProfiles N δ W ten) =
      ∑ q ∈ omega3SieveModuli N D Z, (3 : ℝ) ^ q.primeFactors.card *
        |∑ c ∈ L.filter (fun c => (omega3CofactorValue c).Coprime q),
          (convolutionCoeff W c.1 : ℝ) *
            (if fourthRowTripleGatedBand N δ ten c.1 c.2.2.1 c.2.1 then
              (fourthRowTripleGatedAP N δ c q : ℝ) -
                (fourthRowTripleGatedFibre N δ c).card / (Nat.totient q : ℝ) else 0)| := by
    simp only [fourthRowTripleGatedR1, fourthRowTripleGatedResidual, fourthRowTripleGatedProfiles,
      sum_filter, L, mul_ite, mul_zero]
    apply sum_congr rfl
    intro q _
    congr 2
    apply sum_congr rfl
    intro c _
    split_ifs <;> rfl
  rw [hl]
  apply h.trans_eq
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro q _
  congr 2
  apply sum_congr rfl
  intro e he
  have hm := omega3LayerLabel_mem (mem_filter.mp he).1
  have hgeom := hg _ hm.1
  rw [fourthRowTripleGated_AP_profile hgeom.1 hgeom.2, hm.2]
  simp only [fourthRowTripleGatedLayerCoefficient, L, mul_ite, ite_mul, zero_mul, mul_zero]

theorem fourthRowTripleGated_R1_log (k : ℕ) {δ A : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ ten : Bool,
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ) ^ (1 / 2 - δ)
      fourthRowTripleGatedR1 N (⌊Q⌋₊ + 1) δ (sqrt Q) W (fourthRowTripleGatedProfiles N δ W ten) ≤
        C * N / log (N : ℝ) ^ A := by
  have hη := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num : (0 : ℝ) < 10)
  obtain ⟨C, hC, T1, hT1, hdist⟩ := omega3_balanced_interval_distribution A
    (wuLocalExponent k δ / 10) (omega3LayerConstant k δ) hA hη
    (omega3LayerConstant_pos k δ).le hδ
  obtain ⟨T2, _, hlayers⟩ := omega3_cofactor_common_profile_layers k hδ hδhi
  refine ⟨((omega3LayerCount k δ : ℝ) + 1) * C, by positivity,
    max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb ten W Q
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN4 := hT1.trans hN1
  let L := omega3CofactorLabels N δ (5 / 2) (103 / 25) W
  obtain ⟨hcard, hcoeff, _, _, _⟩ := hlayers N hN2 i Δ V hb (5 / 2) (103 / 25)
    (by norm_num) (by norm_num) (by norm_num)
  have hg := fun c hc => fourthRowTripleGated_geometry (by omega : 2 ≤ N)
    hδ hδhi hb (c := c) hc
  have hj (j : ℕ) :
      (∑ q ∈ omega3SieveModuli N (⌊Q⌋₊ + 1) (sqrt Q), (3 : ℝ) ^ q.primeFactors.card *
        |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
          fourthRowTripleGatedLayerCoefficient N δ W ten j e * omega3ProfileError N q e
            (fourthRowTripleGatedLower N δ (omega3LayerLabel L j e))
            (fourthRowTripleGatedUpper N δ (omega3LayerLabel L j e))|) ≤
        C * N / log (N : ℝ) ^ A := by
    apply hdist N hN1 (omega3LayerSupport L j) (fourthRowTripleGatedLayerCoefficient N δ W ten j)
      (fun e => fourthRowTripleGatedLower N δ (omega3LayerLabel L j e))
      (fun e => fourthRowTripleGatedUpper N δ (omega3LayerLabel L j e))
    · intro e he
      have hm := omega3LayerLabel_mem he
      have h := hg _ hm.1
      exact ⟨hm.2 ▸ h.2.2.1, hm.2 ▸ h.2.2.2.1⟩
    · intro e _
      unfold fourthRowTripleGatedLayerCoefficient
      dsimp only
      split_ifs
      · rw [abs_of_nonneg (hcoeff j e).1]
        exact (hcoeff j e).2.1
      · exact (by simpa only [abs_zero] using (omega3LayerConstant_pos k δ).le)
    · intro e he
      have hm := omega3LayerLabel_mem he
      have h := hg _ hm.1
      exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, by simpa only [hm.2] using h.2.2.2.2.2.2⟩
  have hf := fourthRowTripleGated_R1_layers (N := N) (D := ⌊Q⌋₊ + 1) (δ := δ)
    (Z := sqrt Q) W ten hcard (fun c hc => ⟨(hg c hc).1, (hg c hc).2.1⟩)
  have hs := hf.trans (sum_le_sum fun j _ => hj j)
  simp only [sum_const, card_range, nsmul_eq_mul] at hs
  exact hs.trans (by
    have hlog := log_pos (by exact_mod_cast (show 1 < N by omega) : (1 : ℝ) < N)
    have hh : (omega3LayerCount k δ : ℝ) ≤ (omega3LayerCount k δ : ℝ) + 1 := by linarith
    exact (mul_le_mul_of_nonneg_right hh (by positivity :
      0 ≤ C * N / log (N : ℝ) ^ A)).trans_eq (by ring))

theorem fourthRowTripleGated_R2_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ ten : Bool,
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ) ^ (1 / 2 - δ)
      fourthRowTripleGatedR2 N (⌊Q⌋₊ + 1) δ (sqrt Q) W (fourthRowTripleGatedProfiles N δ W ten) ≤
        ε * boxTheta N Q W := by
  obtain ⟨T, hT4, hpay⟩ := omega3_non_coprime_relative k hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb ten W Q
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hδ hδhi
  have hqN : ∀ q ∈ omega3SieveModuli N (⌊Q⌋₊ + 1) (sqrt Q), q ≤ N := by
    intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hg.2.2.2.2.2.2.1
    dsimp only [Q] at hqd
    omega
  have h := hpay N hN i Δ V hb (5 / 2) (103 / 25) (by norm_num) (by norm_num)
    (by norm_num) (sqrt Q) hg.2.2.2.1 (omega3SieveModuli N (⌊Q⌋₊ + 1) (sqrt Q))
    (filter_subset _ _) hqN
  apply le_trans _ h
  apply sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_trans (sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (card_le_card (filter_subset _ _))) (Nat.cast_nonneg (convolutionCoeff W c.1)))
  exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
    (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end Wu2008DoubleSieve
