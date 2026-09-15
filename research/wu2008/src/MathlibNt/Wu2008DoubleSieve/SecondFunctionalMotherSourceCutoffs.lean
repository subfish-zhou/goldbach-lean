import MathlibNt.Wu2008DoubleSieve.SecondFunctionalParameters
import MathlibNt.Wu2008DoubleSieve.FourthRowMotherPayment

/-! # Cutoff order derived from the original source-box geometry -/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

theorem secondFunctionalMother_source_cutoff_antitone
    {i k N d : ℕ} {δ Δ u v : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hu : 0 < u) (huv : u ≤ v) :
    wuLocalCutoff N δ d v ≤ wuLocalCutoff N δ d u := by
  have hg := wu_buchstab_prime_window_bounds (s := 2) (t := 2)
    hN hδ hδhi hb le_rfl le_rfl (by norm_num) hd
  exact Real.rpow_le_rpow_of_exponent_le hg.2.2.1.le
    (one_div_le_one_div_of_le hu huv)

theorem secondFunctionalMother_source_cutoffs
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 < d ∧ d ≤ N ∧
      wuLocalCutoff N δ d p.S ≤ wuLocalCutoff N δ d p.kappa1 ∧
      wuLocalCutoff N δ d p.kappa1 ≤ wuLocalCutoff N δ d p.kappa2 ∧
      wuLocalCutoff N δ d p.kappa2 ≤ wuLocalCutoff N δ d p.kappa3 ∧
      wuLocalCutoff N δ d p.kappa3 ≤ wuLocalCutoff N δ d p.s := by
  have hs : 0 < p.s := lt_of_lt_of_le zero_lt_one hp.one_le_s
  have h3 := hs.trans_le hp.s_le_kappa3
  have h2 := h3.trans hp.kappa3_lt_kappa2
  have h1 := h2.trans hp.kappa2_lt_kappa1
  have hg := wu_buchstab_prime_window_bounds (s := 2) (t := 2)
    hN hδ hδhi hb le_rfl le_rfl (by norm_num) hd
  exact ⟨hg.1, hg.2.1,
    secondFunctionalMother_source_cutoff_antitone hN hδ hδhi hb hd h1 hp.kappa1_le_S,
    secondFunctionalMother_source_cutoff_antitone hN hδ hδhi hb hd h2 hp.kappa2_lt_kappa1.le,
    secondFunctionalMother_source_cutoff_antitone hN hδ hδhi hb hd h3 hp.kappa3_lt_kappa2.le,
    secondFunctionalMother_source_cutoff_antitone hN hδ hδhi hb hd hs hp.s_le_kappa3⟩

end Wu2008DoubleSieve
