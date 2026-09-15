import MathlibNt.Wu2008DoubleSieve.HighSixOmega1Rosser

namespace Wu2008DoubleSieve.HighSix
open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- A uniform envelope for the full selected modulus pN at the moving cutoff. -/
theorem single_modulus_envelope {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N) :
    ((p*N : ℕ) : ℝ) ≤ (z N δ p)^(50 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpN : p ≤ N := by
    have h := (mem_primeWindow.mp hp).2.2.2.le.trans
      (rpow_le_rpow_of_exponent_le hN1 (show right ≤ 1 by norm_num [right]))
    rw [rpow_one] at h
    exact_mod_cast h
  calc
    _ ≤ (N : ℝ)^(2 : ℝ) := by
      norm_cast
      nlinarith
    _ = ((N : ℝ)^(1/25 : ℝ))^(50 : ℝ) := by
      rw [← rpow_mul (Nat.cast_nonneg N)]; norm_num
    _ ≤ _ := rpow_le_rpow (by positivity) (inner_lower_cutoff hN hδ hδhi hp) (by norm_num)

/-- Classical upper normalization at z_p, with the full pN and no source box.
All density and local-product thresholds precede N and p. -/
theorem single_normalized_point_upper {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ p : ℕ, p ∈ P N →
      ordinaryRosserMainSum true N p (wuVariableRosserLevel N δ p) (z N δ p) ≤
        (wuUpperCoefficient S+6*η)*(4*wuSingularSeries (p*N)/log (R N δ p)) := by
  have hρ : 0 < exp eulerMascheroniConstant*η/2 := by positivity
  obtain ⟨Z, hdensity⟩ := ordinaryRosser_upper_density_canonical_extended_local hρ
  obtain ⟨Z1, hZ1⟩ := eventually_atTop.mp
    (eventually_localSieveProduct_relative 50 η (by norm_num) hη)
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^(1/25 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/25)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hpow.eventually (eventually_ge_atTop (max 2 (max Z Z1))))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN he p hp
  have hN2 : 2 ≤ N := by omega
  have hz := (hT N (by omega)).trans (inner_lower_cutoff hN2 hδ hδhi hp)
  have hz2 : 2 ≤ z N δ p := (le_max_left _ _).trans hz
  have hzZ : Z ≤ z N δ p := (le_max_left Z Z1).trans ((le_max_right _ _).trans hz)
  have hzZ1 : Z1 ≤ z N δ p := (le_max_right Z Z1).trans ((le_max_right _ _).trans hz)
  have hr := ratio_bounds hN2 hδ hδhi hp
  have hR0 : 0 < R N δ p := zero_lt_one.trans hr.1
  have hlR : 0 < log (R N δ p) := log_pos hr.1
  have hlz : log (z N δ p) = (1/S)*log (R N δ p) := log_rpow hR0 _
  have hS : S ≠ 0 := by norm_num [S]
  have hsarg : S = log (R N δ p)/log (z N δ p) := by
    rw [hlz]
    field_simp
  have hM0 : 0 < p*N := Nat.mul_pos (mem_primeWindow.mp hp).1.pos (by omega)
  have hlocal := hZ1 (z N δ p) hzZ1 (p*N) hM0 (he.mul_left p)
    (single_modulus_envelope hN2 hδ hδhi hp)
  have hnormal : 2*S*wuSingularSeries (p*N)/(exp eulerMascheroniConstant*log (R N δ p)) =
      2*exp (-eulerMascheroniConstant)*wuSingularSeries (p*N)/log (z N δ p) := by
    rw [hlz, exp_neg]
    field_simp
  rw [← hnormal] at hlocal
  have hn0 : 0 < 2*S*wuSingularSeries (p*N)/(exp eulerMascheroniConstant*log (R N δ p)) := by
    have := wuSingularSeries_pos _ hM0
    have : 0 < S := by norm_num [S]
    positivity
  have hprod : localSieveProduct (p*N) (z N δ p) ≤
      (1+η)*(2*S*wuSingularSeries (p*N)/(exp eulerMascheroniConstant*log (R N δ p))) := by
    apply (div_le_iff₀ hn0).mp
    linarith [(le_abs_self (_ : ℝ)).trans hlocal]
  have hF : 0 ≤ jr1965F S+exp eulerMascheroniConstant*η/2 :=
    add_nonneg (jr1965F_pos (by norm_num [S])).le hρ.le
  have hd := hdensity N p he (z N δ p) (R N δ p) S hzZ hz2 hR0 hsarg
    (by norm_num [S]) (by norm_num [S])
  have hn := canonical_upper_extended_normalization_budget
    (show 1 ≤ S by norm_num [S]) (show S ≤ 4 by norm_num [S])
    (wuSingularSeries_pos _ hM0).le hlR hη.le hη1
  exact hd.trans ((mul_le_mul_of_nonneg_left hprod hF).trans hn)

/-- The original B6 is exactly the full li/phi/pN main, not an asymptotic proxy. -/
theorem single_normalized_main_upper {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      singleMain N δ ≤ (wuUpperCoefficient S+6*η)*B6 N δ := by
  obtain ⟨T,hT4,hT⟩ := single_normalized_point_upper hδ hδhi hη hη1
  refine ⟨T,hT4,?_⟩
  intro N hN he
  rw [B6_sum, mul_sum]
  apply sum_le_sum
  intro p hp
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast (show 2 ≤ N by omega))
  have h := mul_le_mul_of_nonneg_left (hT N hN he p hp)
    (div_nonneg hli (Nat.cast_nonneg (Nat.totient p)))
  convert h using 1
  unfold thetaAtom
  ring

/-- Actual Omega1 endpoint. Both the normalization and signed BV budgets are
selected internally; the coefficient two is the literal code coefficient. -/
theorem omega1_upper_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      O1 N δ ≤ 2*wuUpperCoefficient S*B6 N δ + ε*truncatedSixthMassScale N := by
  let η := min 1 (ε/11520)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηfee : 5760*η ≤ ε/2 := by
    have h := min_le_right 1 (ε/11520)
    dsimp [η]
    linarith
  obtain ⟨T1,hT14,hT1⟩ := single_normalized_main_upper hδ hδhi hη hη1
  obtain ⟨T2,_,hT2⟩ := omega1_rosser_paid hδ hδhi (half_pos hε)
  obtain ⟨T3,_,hT3⟩ := B6_total_mass hδ hδhi
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hm := hT1 N (by omega) he
  have ho := hT2 N (by omega)
  have hb := hT3 N (by omega) he
  have hs : 0 ≤ truncatedSixthMassScale N := by
    have hC := (wuSingularSeries_pos N (by omega : 0 < N)).le
    unfold truncatedSixthMassScale
    positivity
  have hfee : 12*η*B6 N δ ≤ (ε/2)*truncatedSixthMassScale N := by
    calc
      _ ≤ 12*η*(480*truncatedSixthMassScale N) :=
        mul_le_mul_of_nonneg_left hb.2 (by positivity)
      _ = (5760*η)*truncatedSixthMassScale N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hηfee hs
  nlinarith

/-- Actual consumption of the existing Omega2 integral mother. O3 stays
literal; neither a full Psi endpoint nor numerical strength is asserted. -/
theorem count_omega1_integral_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      2*C6 N ≤ (2*wuUpperCoefficient S-J)*B6 N δ + O3 N δ +
        ε*truncatedSixthMassScale N := by
  obtain ⟨T1,hT14,hT1⟩ := omega1_upper_paid hδ hδhi (half_pos hε)
  obtain ⟨T2,_,hT2⟩ := count_integral_paid hδ hδhi (half_pos hε)
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have ho := hT1 N (by omega) he
  have hc := hT2 N (by omega) he
  nlinarith

end Wu2008DoubleSieve.HighSix
