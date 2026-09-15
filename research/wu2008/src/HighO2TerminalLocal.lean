import HighO2TerminalGeometry

namespace HighO2Terminal
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery HighOmega2
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

/-- A bounded monotone extension only for the quadrature interface. It is
literally log(x-1)-4ε at every actual lower ratio and every source integral u. -/
def logCoefficient (ε x : ℝ) : ℝ := log (max 2 x - 1)-4*ε

def apAtom (N Q d : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 (Q/d)).filter (fun q => q.Coprime (d*N)), |primeAPError N (d*q) N|

theorem apAtom_nonneg (N Q d : ℕ) : 0 ≤ apAtom N Q d :=
  sum_nonneg (fun _ _ => abs_nonneg _)

/-- Local normalized lower with the actual AP kernel, before summation.
The threshold is uniform in d and the variable ratio. -/
theorem local_count_lower {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ d : ℕ, 0 < d →
      (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta) → ∀ s : ℝ, 2 ≤ s → s ≤ 4 →
      (log (s-1)-4*ε)*(4*logarithmicIntegral N *
        (wuSingularSeries (d*N)/((Nat.totient d : ℝ)*log ((N : ℝ)^(1/2-δ)/d)))) -
        apAtom N (convolutionModulusCutoff N δ) d ≤
      (sourceSieveCount N d (d*N) (wuLocalCutoff N δ d s) : ℝ) := by
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨Z,hL⟩ := ordinaryRosser_lower_density_canonical_local
    (show 0 < exp eulerMascheroniConstant*ε/2 by positivity)
  obtain ⟨T0,hT02,hlocal⟩ := local_normalization hδ hη hε
  obtain ⟨T1,hT1⟩ := eventually_atTop.mp
    ((((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (max 2 Z)))
  refine ⟨max 4 (max T0 T1),le_max_left _ _,?_⟩
  intro N hN he d hd hsize s hs hs4
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN0 : T0 ≤ N := (le_max_left T0 T1).trans ((le_max_right _ _).trans hN)
  have hN1 : T1 ≤ N := (le_max_right T0 T1).trans ((le_max_right _ _).trans hN)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hq : 1 < (N : ℝ)^(1/2-δ)/d := (one_lt_div (by exact_mod_cast hd)).mpr
    (hsize.trans_lt (rpow_lt_rpow_of_exponent_lt hNr (by linarith)))
  have hz := (hT1 N hN1).trans (cutoff_lower (show 2 ≤ N by omega) hd hη
    (show 0 < s by linarith) (show s ≤ 10 by linarith) hsize)
  have hl := hL N d he _ _ s ((le_max_right _ _).trans hz) ((le_max_left _ _).trans hz)
    (by linarith) (log_div_log_rpow_eq hq (by linarith)).symm hs hs4
  have hn := canonical_lower_normalization_budget hs hs4
    (wuSingularSeries_pos _ (Nat.mul_pos hd (by omega))) (log_pos hq) hε.le hε1
    (hlocal N hN0 he d hd hsize s (by linarith) (by linarith))
  have hnorm := hn.trans hl
  have hli : 0 ≤ logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N/(2*log N)).trans (box_trueLi_lower hN4)
  have hweighted := mul_le_mul_of_nonneg_left hnorm
    (div_nonneg hli (Nat.cast_nonneg (Nat.totient d)))
  have hfinite := ordinaryRosser_lower_finite (N := N) (d := d)
    (variableRosser_geometry hq (show 1 ≤ s by linarith)).2.1
  have hap := ordinaryRosserRemainder_le_AP (upper := false) (N := N)
    (d := d) (wuLocalCutoff N δ d s) (wuVariableRosserLevel_eq_combined N d δ).le
  change |ordinaryRosserRemainder false N d (wuVariableRosserLevel N δ d)
    (wuLocalCutoff N δ d s)| ≤ apAtom N (convolutionModulusCutoff N δ) d at hap
  have heq : (logarithmicIntegral N/(Nat.totient d : ℝ))*
      ((log (s-1)-4*ε)*(4*wuSingularSeries (d*N)/log ((N : ℝ)^(1/2-δ)/d))) =
    (log (s-1)-4*ε)*(4*logarithmicIntegral N *
      (wuSingularSeries (d*N)/((Nat.totient d : ℝ)*log ((N : ℝ)^(1/2-δ)/d)))) := by ring
  rw [heq] at hweighted
  dsimp only [wuVariableRosserLevel,wuLocalCutoff] at hap hweighted ⊢
  linarith [(abs_le.mp hap).1]

/-- Every actual selected prime is lower-sieved at exactly the original
fixed cutoff. The singular-factor identity is exact, not a p versus p-2
asymptotic replacement. The full Omega2 later retains repeated primes. -/
theorem original_atom_lower {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ, 0 < Δ →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → 2 ≤ t-t/s →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      (4*logarithmicIntegral N)*(wuSingularSeries (d*N)/((Nat.totient d : ℝ)*
          log ((N : ℝ)^(1/2-δ)/d))) *
        (logCoefficient ε (ratio N d p δ t)/(((p : ℝ)-2)*
          (1-log (p : ℝ)/log ((N : ℝ)^(1/2-δ)/d)))) -
        apAtom N (convolutionModulusCutoff N δ) (d*p) ≤
        (sourceSieveCount N (d*p) (d*N) (wuLocalCutoff N δ d t) : ℝ) := by
  obtain ⟨T0,hT04,hT⟩ := local_count_lower hδ hε hε1
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨T1,hlarge⟩ := eventually_atTop.mp
    ((((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hΔ V hV hr s t hs _hst ht ht5 hc d hd p hp
  have hN0 : T0 ≤ N := (le_max_left _ _).trans hN
  have hN4 := hT04.trans hN0
  have hp' := mem_primeWindow.mp hp
  have hpN : p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) :=
    mem_primeWindow.mpr ⟨hp'.1,(Nat.coprime_mul_iff_right.mp hp'.2.1).2,hp'.2.2⟩
  have hg := full_prime_geometry (show 2 ≤ N by omega) hδ hδhi hΔ hV hr hd hs ht ht5 hpN
  have hsp := original_support (show 2 ≤ N by omega) hδ hδhi hΔ hV hr hd
  have hu := ratio_domain hsp.2.2.2.2 hs ht ht5 hc hpN
  have hl := hT N hN0 he (d*p) (Nat.mul_pos hsp.1 hp'.1.pos) hg.2.2
    (ratio N d p δ t) hu.1 hu.2
  rw [ratio_cutoff hsp.2.2.2.2 hp'.1.pos (by linarith) (by linarith [hu.1]),
    omega2_source_count_prime_modulus_eq N d hp'.1 hp'.2.2.1] at hl
  have hp4 : (4 : ℝ) ≤ p := (hlarge N ((le_max_right _ _).trans hN)).trans hg.1
  have hpd : ¬p ∣ d := hp'.1.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_right.mp hp'.2.1).1
  have hw := wu_inserted_theta_weight (show 0 < N by omega) hsp.1 hp'.1
    (show 2 < p by exact_mod_cast (show (2 : ℝ) < p by linarith))
    (Nat.coprime_mul_iff_right.mp hp'.2.1).2 hsp.2.2.2.2
  simp only [if_neg hpd] at hw
  rw [Nat.cast_mul] at hl
  rw [hw] at hl
  convert hl using 1
  dsimp [logCoefficient]
  rw [max_eq_right hu.1]
  simp only [div_mul_eq_div_div]
  ring

end
end HighO2Terminal
