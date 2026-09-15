import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitMassLogCap
import MathlibNt.Wu2008DoubleSieve.Omega3XNormalization

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitSource
open Finset Real HighUnit
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- Elementary near-one coefficient for the genuine logarithmic integral. -/
theorem trueLi_near_one {τ : ℝ} (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      (N : ℝ) / log N ≤ (1 + τ) * logarithmicIntegral N := by
  obtain ⟨T, hT⟩ := exists_nat_ge (2 * (1 + τ) / τ)
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN4' : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hTN : (T : ℝ) ≤ N := by exact_mod_cast ((le_max_right 4 T).trans hN)
  have hp : 2 * (1 + τ) ≤ (N : ℝ) * τ := (div_le_iff₀ hτ).mp (hT.trans hTN)
  have hl : 0 < log (N : ℝ) := log_pos (by linarith)
  have hli := box_trueLi_sub_lower (show (2 : ℝ) ≤ 2 by norm_num)
    (show (2 : ℝ) ≤ N by linarith)
  have hli2 : 0 ≤ logarithmicIntegral 2 :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl (by norm_num)
  calc
    _ ≤ (1 + τ) * (((N : ℝ) - 2) / log N) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hl.le
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- A deliberately coarse compact bound, used only in the epsilon budget. -/
theorem unitLogCap_pair_compact {a2 a b : ℝ}
    (ha : 1/10 ≤ a2) (haa : a2 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/2) :
    0 ≤ unitLogCap20 a2 a b + unitLogCap21 a b ∧
      unitLogCap20 a2 a b + unitLogCap21 a b ≤ 2000 := by
  have ha2 : 0 < a2 := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have h10 : (1:ℝ) ≤ a / a2 := (le_div_iff₀ ha2).mpr (by linarith)
  have h11 : (1:ℝ) ≤ b / a := (le_div_iff₀ ha0).mpr (by linarith)
  have h50 : a / a2 ≤ 5 := (div_le_iff₀ ha2).mpr (by linarith)
  have h51 : b / a ≤ 5 := (div_le_iff₀ ha0).mpr (by linarith)
  have hl0 : 0 ≤ log (a/a2) := log_nonneg h10
  have hl1 : 0 ≤ log (b/a) := log_nonneg h11
  have hl5 : log (a/a2) ≤ 5 := (log_le_sub_one_of_pos (div_pos ha0 ha2)).trans (by linarith)
  have hl6 : log (b/a) ≤ 5 := (log_le_sub_one_of_pos (div_pos hb0 ha0)).trans (by linarith)
  have h20 : unitLogCap20 a2 a b ≤ 1000 := by
    unfold unitLogCap20
    calc
      _ ≤ (5:ℝ) * 5^3 / (24*(1/10)) := by gcongr; linarith
      _ ≤ 1000 := by norm_num
  have h21 : unitLogCap21 a b ≤ 1000 := by
    unfold unitLogCap21
    calc
      _ ≤ (5:ℝ)^5 / (720*(1/10)) := by gcongr; linarith
      _ ≤ 1000 := by norm_num
  constructor
  · unfold unitLogCap20 unitLogCap21
    positivity
  · linarith

/-- Pointwise comparison retains C(N), replacing neither totient nor C(d*N)
by equalities. The logarithmic domain is supplied by the original source box. -/
theorem unitLogMass_theta_comparison {i k N : ℕ} {δ Δ τ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (hτ : 0 ≤ τ)
    (hli : (N:ℝ) / log N ≤ (1+τ) * logarithmicIntegral N) :
    wuSingularSeries N / log N * unitLogMass N δ (convolutionWuWindows N Δ V) ≤
      (1+τ)/4 * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let W := convolutionWuWindows N Δ V
  let Q := (N:ℝ)^(1/2-δ)
  have hC0 := (wuSingularSeries_pos N (by omega)).le
  have hli0 : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  have hmass0 : 0 ≤ ∑ d ∈ boxConvolutionSupport W,
      (convolutionCoeff W d : ℝ) / ((d:ℝ) * log (Q/d)) := by
    apply sum_nonneg
    intro d hd
    have hR := (omega3XPhi_source_bounds (by omega) hδ hδhi hb hd).2.1
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (log_pos hR).le)
  have hsum : wuSingularSeries N *
      (∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) / ((d:ℝ) * log (Q/d))) ≤
      ∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) * wuSingularSeries (d*N) /
          ((Nat.totient d : ℝ) * log (Q/d)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hs := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
    have hd0 := (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1
    have hd0' : (0:ℝ) < d := by exact_mod_cast hd0
    have ht0 : (0:ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
    have ht : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
    have hl : 0 < log (Q/d) := log_pos hs.2.1
    have hC := wuSingularSeries_le_mul (N := N) (by omega) hd0
    have hCd0 := hC0.trans hC
    calc
      _ = (convolutionCoeff W d : ℝ) * wuSingularSeries N /
          ((d:ℝ)*log (Q/d)) := by ring
      _ ≤ _ := by gcongr
  calc
    _ = ((N:ℝ) / log N) * (wuSingularSeries N *
        ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) / ((d:ℝ) * log (Q/d))) := by
      unfold unitLogMass
      dsimp only [W, Q]
      ring
    _ ≤ ((1+τ)*logarithmicIntegral N) * (wuSingularSeries N *
        ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) / ((d:ℝ) * log (Q/d))) :=
      mul_le_mul_of_nonneg_right hli (mul_nonneg hC0 hmass0)
    _ ≤ ((1+τ)*logarithmicIntegral N) *
        (∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) * wuSingularSeries (d*N) /
            ((Nat.totient d : ℝ) * log (Q/d))) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by linarith) hli0)
    _ = _ := by unfold boxTheta; dsimp only [W, Q]; ring

/-- The reciprocal-mass error pays Theta/2 with the full, varying C(N). -/
theorem reciprocalMass_theta_payment {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) :
    wuSingularSeries N / log N * ((N:ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) ≤
      boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) / 2 := by
  have h := omega3_source_theta_lower_singular hN hδ hδhi hb
  have heq : 2 * (wuSingularSeries N / log N * ((N:ℝ) / log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) =
      2 * wuSingularSeries N * (N:ℝ) / log N ^ 2 *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by ring
  linarith

/-- Actual boxed masses normalized to the original Theta. The common threshold
precedes N, every source box, and all mother parameters. The leading coefficient
is the literal sum of logarithmic caps divided by four, not its compact bound. -/
theorem mother_boxed_mass_pair_theta (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      (wuSingularSeries N / log N) *
        (boxedSigma20 N δ W (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
          boxedSigma21 N δ W (fun _ => 1/p.kappa3) (fun _ => 1/p.s)) ≤
      ((unitLogCap20 (1/p.kappa2) (1/p.kappa3) (1/p.s) +
          unitLogCap21 (1/p.kappa3) (1/p.s))/4 + epsilon) *
        boxTheta N ((N:ℝ)^(1/2-δ)) W := by
  obtain ⟨T₁,hT₁4,hT₁⟩ := mother_boxed_mass_pair_log_cap k hδ hδhi he
  obtain ⟨T₂,hT₂4,hT₂⟩ := trueLi_near_one (show 0 < epsilon/1000 by positivity)
  refine ⟨max T₁ T₂, hT₁4.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p hp hs
  have hN₁ := (le_max_left T₁ T₂).trans hN
  have hN₂ := (le_max_right T₁ T₂).trans hN
  have hN4 := hT₂4.trans hN₂
  let W := convolutionWuWindows N Δ V
  let K := unitLogCap20 (1/p.kappa2) (1/p.kappa3) (1/p.s) +
    unitLogCap21 (1/p.kappa3) (1/p.s)
  let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) W
  obtain ⟨ha,haa,hab,hbhi⟩ := parameter_log_cap_bounds hp hs
  have hK : 0 ≤ K ∧ K ≤ 2000 := unitLogCap_pair_compact ha haa hab hbhi
  have hlog : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hmass0 : 0 ≤ boxConvolutionReciprocalMass W :=
    sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  have herr := reciprocalMass_theta_payment hN4 hδ hδhi hb
  have hΘ : 0 ≤ Θ := by
    have hlhs : 0 ≤ wuSingularSeries N / log N * ((N:ℝ) / log N) *
        boxConvolutionReciprocalMass W := by positivity
    change _ ≤ Θ / 2 at herr
    linarith
  have hunit := unitLogMass_theta_comparison hN4 hδ hδhi hb
    (show 0 ≤ epsilon/1000 by positivity) (hT₂ N hN₂)
  have hm := hT₁ N hN₁ i Δ V hb p hp hs
  dsimp only at hm ⊢
  change _ ≤ K * unitLogMass N δ W +
    epsilon * ((N:ℝ) / log N) * boxConvolutionReciprocalMass W at hm
  change _ ≤ (1+epsilon/1000)/4 * Θ at hunit
  change _ ≤ Θ/2 at herr
  change _ ≤ (K/4+epsilon)*Θ
  calc
    _ ≤ (wuSingularSeries N / log N) * (K * unitLogMass N δ W +
        epsilon * ((N:ℝ) / log N) * boxConvolutionReciprocalMass W) :=
      mul_le_mul_of_nonneg_left hm (div_nonneg hC hlog.le)
    _ = K * (wuSingularSeries N / log N * unitLogMass N δ W) +
        epsilon * (wuSingularSeries N / log N * ((N:ℝ) / log N) *
          boxConvolutionReciprocalMass W) := by ring
    _ ≤ K * ((1+epsilon/1000)/4 * Θ) + epsilon * (Θ/2) :=
      add_le_add (mul_le_mul_of_nonneg_left hunit hK.1)
        (mul_le_mul_of_nonneg_left herr he.le)
    _ = (K * (1+epsilon/1000)/4 + epsilon/2)*Θ := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hΘ
      have hbudget : epsilon * K ≤ epsilon * 2000 :=
        mul_le_mul_of_nonneg_left hK.2 he.le
      nlinarith only [hbudget]

end Wu2008DoubleSieve.HighUnitSource
