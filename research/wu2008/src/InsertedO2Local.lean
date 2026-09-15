import InsertedO2Geometry

namespace InsertedO2
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery HighOmega2 HighO2Terminal
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

/-- Parameterized residual-gap admission, specialized downstream to η/2.
Uses the existing canonical local product normalization verbatim. -/
theorem local_count {δ η ε : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ d : ℕ, 0 < d →
      (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η) → ∀ s : ℝ, 2 ≤ s → s ≤ 4 →
      (log (s-1)-4*ε)*(4*logarithmicIntegral N *
        (wuSingularSeries (d*N)/((Nat.totient d : ℝ)*log ((N : ℝ)^(1/2-δ)/d)))) -
        apAtom N (convolutionModulusCutoff N δ) d ≤
      (sourceSieveCount N d (d*N) (wuLocalCutoff N δ d s) : ℝ) := by
  obtain ⟨Z,hL⟩ := ordinaryRosser_lower_density_canonical_local
    (show 0 < exp eulerMascheroniConstant*ε/2 by positivity)
  obtain ⟨T0,_,hlocal⟩ := local_normalization hδ hη hε
  obtain ⟨T1,hgrow⟩ := eventually_atTop.mp
    ((((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (max 2 Z)))
  refine ⟨max 4 (max T0 T1),le_max_left _ _,?_⟩
  intro N hN he d hd hsize s hs hs4
  have hN4 : 4 ≤ N := by omega
  have hN0 : T0 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hq : 1 < (N : ℝ)^(1/2-δ)/d := (one_lt_div (by exact_mod_cast hd)).mpr
    (hsize.trans_lt (rpow_lt_rpow_of_exponent_lt hNr (by linarith)))
  have hz := (hgrow N hN1).trans (cutoff_lower (show 2 ≤ N by omega) hd hη
    (show 0 < s by linarith) (show s ≤ 10 by linarith) hsize)
  have hmain := (canonical_lower_normalization_budget hs hs4
    (wuSingularSeries_pos _ (Nat.mul_pos hd (by omega))) (log_pos hq) hε.le hε1
    (hlocal N hN0 he d hd hsize s (by linarith) (by linarith))).trans
      (hL N d he _ _ s ((le_max_right _ _).trans hz) ((le_max_left _ _).trans hz)
        (by linarith) (log_div_log_rpow_eq hq (by linarith)).symm hs hs4)
  have hli : 0 ≤ logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N/(2*log N)).trans (box_trueLi_lower hN4)
  have hw := mul_le_mul_of_nonneg_left hmain
    (div_nonneg hli (Nat.cast_nonneg (Nat.totient d)))
  have hf := ordinaryRosser_lower_finite (N := N) (d := d)
    (variableRosser_geometry hq (show 1 ≤ s by linarith)).2.1
  have ha := ordinaryRosserRemainder_le_AP (upper := false) (N := N)
    (d := d) (wuLocalCutoff N δ d s) (wuVariableRosserLevel_eq_combined N d δ).le
  change |ordinaryRosserRemainder false N d (wuVariableRosserLevel N δ d)
    (wuLocalCutoff N δ d s)| ≤ apAtom N (convolutionModulusCutoff N δ) d at ha
  have hw' : (log (s-1)-4*ε)*(4*logarithmicIntegral N *
      (wuSingularSeries (d*N)/((Nat.totient d : ℝ)*log ((N : ℝ)^(1/2-δ)/d)))) ≤
    logarithmicIntegral N/(Nat.totient d : ℝ)*
      ordinaryRosserMainSum false N d (wuVariableRosserLevel N δ d) (wuLocalCutoff N δ d s) := by
    calc
      _ = (logarithmicIntegral N/(Nat.totient d : ℝ))*
        ((log (s-1)-4*ε)*(4*wuSingularSeries (d*N)/log ((N : ℝ)^(1/2-δ)/d))) := by ring
      _ ≤ _ := hw
  dsimp only [wuVariableRosserLevel,wuLocalCutoff] at ha hw' ⊢
  linarith [(abs_le.mp ha).1]

/-- Exact selected atom on the full interval. The half-gap, parameter strip,
cutoff identity and singular-factor identity are all actually consumed. -/
theorem selected_atom {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ d : ℕ, 0 < d →
      (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta) →
      ∀ s t : ℝ, 2 ≤ s → 3 ≤ t → t ≤ 5 → 2 ≤ t-t/s →
      ∀ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      (4*logarithmicIntegral N)*(wuSingularSeries (d*N)/((Nat.totient d : ℝ)*
          log ((N : ℝ)^(1/2-δ)/d))) *
        (logCoefficient ε (ratio N d p δ t)/(((p : ℝ)-2)*
          (1-log (p : ℝ)/log ((N : ℝ)^(1/2-δ)/d)))) -
        apAtom N (convolutionModulusCutoff N δ) (d*p) ≤
        (sourceSieveCount N (d*p) (d*N) (wuLocalCutoff N δ d t) : ℝ) := by
  have he : 0 < highEta := by norm_num [highEta]
  obtain ⟨T0,hT04,hcount⟩ := local_count hδ (half_pos he) hε hε1
  obtain ⟨T1,hgrow⟩ := eventually_atTop.mp
    ((((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN hEven d hd hsize s t hs ht ht5 hc p hp
  have hN0 : T0 ≤ N := by omega
  have hN4 := hT04.trans hN0
  have hh := mem_primeWindow.mp hp
  have hpN := selected_subset_original N d _ _ hp
  have hg := full_prime_half_gap (show 2 ≤ N by omega) hδ hd hsize hs ht ht5 hpN
  have hq := (residual_level (show 2 ≤ N by omega) hδ hd hsize).2.2
  have hu := ratio_domain hq hs ht ht5 hc hpN
  have hl := hcount N hN0 hEven (d*p) (Nat.mul_pos hd hh.1.pos) hg.2.2
    (ratio N d p δ t) hu.1 hu.2
  rw [ratio_cutoff hq hh.1.pos (by linarith) (by linarith [hu.1]),
    omega2_source_count_prime_modulus_eq N d hh.1 hh.2.2.1] at hl
  have hp4 : (4 : ℝ) ≤ p := (hgrow N ((le_max_right _ _).trans hN)).trans hg.1
  have hpd : ¬p ∣ d := hh.1.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_right.mp hh.2.1).1
  have hw := wu_inserted_theta_weight (show 0 < N by omega) hd hh.1
    (show 2 < p by exact_mod_cast (show (2 : ℝ) < p by linarith))
    (Nat.coprime_mul_iff_right.mp hh.2.1).2 hq
  simp only [if_neg hpd] at hw
  rw [Nat.cast_mul,hw] at hl
  convert hl using 1
  dsimp [logCoefficient]
  rw [max_eq_right hu.1]
  simp only [div_mul_eq_div_div]
  ring

end
end InsertedO2
