import MathlibNt.SieveTheory.LiLiuGoldbachB10SieveProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open scoped BigOperators
open Classical

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private def S1SieveProductLowerOmittedPrimes (N Z : ℕ) : Finset ℕ :=
  N.primeFactors.filter (fun p => 2 < p ∧ Z ≤ p)

private noncomputable def S1SieveProductLowerOmittedCorrection (N Z : ℕ) : ℝ :=
  (S1SieveProductLowerOmittedPrimes N Z).prod SingularSeries.liuCorrectionFactor

private theorem S1SieveProductLower_log_lower_of_two_mul_exp_le
    {A : ℝ} {Z : ℕ} (hZ : 2 ≤ Z)
    (hZA : 2 * Real.exp A ≤ (Z : ℝ)) :
    A ≤ Real.log ((Z - 1 : ℕ) : ℝ) := by
  have hExp : Real.exp A ≤ ((Z - 1 : ℕ) : ℝ) := by
    have hmid : Real.exp A ≤ (Z : ℝ) / 2 := by
      nlinarith
    have hhalf : (Z : ℝ) / 2 ≤ ((Z - 1 : ℕ) : ℝ) := by
      have hnat : Z ≤ 2 * (Z - 1) := by omega
      have hcast : (Z : ℝ) ≤ 2 * ((Z - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      nlinarith
    exact hmid.trans hhalf
  have hlog := Real.log_le_log (Real.exp_pos A) hExp
  simpa [Real.log_exp] using hlog

private theorem S1SieveProductLower_absConst_div_log_le
    {δ C : ℝ} (hδ : 0 < δ) {Z : ℕ} (hZ : 3 ≤ Z)
    (hZA :
      2 * Real.exp (|C| / (δ * Real.exp (-Real.eulerMascheroniConstant))) ≤ (Z : ℝ)) :
    |C| / Real.log ((Z - 1 : ℕ) : ℝ) ≤
      δ * Real.exp (-Real.eulerMascheroniConstant) := by
  have hE : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
  have hL :
      |C| / (δ * Real.exp (-Real.eulerMascheroniConstant)) ≤
        Real.log ((Z - 1 : ℕ) : ℝ) :=
    S1SieveProductLower_log_lower_of_two_mul_exp_le (by omega) hZA
  have hδE : 0 < δ * Real.exp (-Real.eulerMascheroniConstant) := mul_pos hδ hE
  have hlogPos : 0 < Real.log ((Z - 1 : ℕ) : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < Z - 1 by omega))
  have hmul := mul_le_mul_of_nonneg_left hL hδE.le
  have hcancel :
      (δ * Real.exp (-Real.eulerMascheroniConstant)) *
          (|C| / (δ * Real.exp (-Real.eulerMascheroniConstant))) = |C| := by
    field_simp [hδ.ne', (Real.exp_pos _).ne']
  have hbound : |C| ≤
      (δ * Real.exp (-Real.eulerMascheroniConstant)) * Real.log ((Z - 1 : ℕ) : ℝ) := by
    simpa [hcancel] using hmul
  exact (div_le_iff₀ hlogPos).2 <| by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hbound

private theorem S1SieveProductLower_liuCorrectionTruncated_eq_smallFactors
    {N Z : ℕ} (hN : 0 < N) (hZ : 1 ≤ Z) :
    SingularSeries.liuCorrectionTruncated N (Z - 1) =
      (N.primeFactors.filter (fun p => 2 < p ∧ p < Z)).prod
        SingularSeries.liuCorrectionFactor := by
  classical
  have hrange : Finset.range (Z - 1 + 1) = Finset.range Z := by
    rw [Nat.sub_add_cancel hZ]
  unfold SingularSeries.liuCorrectionTruncated
  rw [hrange, ← Finset.prod_filter]
  congr 1
  ext p
  constructor
  · intro hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨hpbase, hpdvd⟩
    rw [Finset.mem_filter, Finset.mem_range] at hpbase
    rcases hpbase with ⟨hpZ, hpPrime, hp2⟩
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hpPrime, hpdvd, hN.ne'⟩, hp2, hpZ⟩
  · intro hp
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    rcases hp with ⟨⟨hpPrime, hpdvd, _⟩, hp2, hpZ⟩
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨hpZ, hpPrime, hp2⟩, hpdvd⟩

private theorem S1SieveProductLower_liuCorrection_eq_truncated_mul_omitted
    {N Z : ℕ} (hN : 0 < N) (hZ : 1 ≤ Z) :
    SingularSeries.liuCorrection N =
      SingularSeries.liuCorrectionTruncated N (Z - 1) *
        S1SieveProductLowerOmittedCorrection N Z := by
  classical
  let A := N.primeFactors.filter (fun p => 2 < p)
  have hsplit := Finset.prod_filter_mul_prod_filter_not A
    (fun p => p < Z) SingularSeries.liuCorrectionFactor
  have hsmallSet :
      ((N.primeFactors.filter fun p => 2 < p).filter fun p => p < Z) =
        N.primeFactors.filter (fun p => 2 < p ∧ p < Z) := by
    ext p
    simp [and_assoc]
  have hlargeSet :
      ((N.primeFactors.filter fun p => 2 < p).filter fun p => ¬ p < Z) =
        S1SieveProductLowerOmittedPrimes N Z := by
    ext p
    simp [S1SieveProductLowerOmittedPrimes, not_lt, and_assoc]
  rw [S1SieveProductLower_liuCorrectionTruncated_eq_smallFactors hN hZ,
    SingularSeries.liuCorrection, S1SieveProductLowerOmittedCorrection]
  calc
    (N.primeFactors.filter fun p => 2 < p).prod SingularSeries.liuCorrectionFactor =
        ((N.primeFactors.filter fun p => 2 < p).filter fun p => p < Z).prod
            SingularSeries.liuCorrectionFactor *
          ((N.primeFactors.filter fun p => 2 < p).filter fun p => ¬ p < Z).prod
            SingularSeries.liuCorrectionFactor := hsplit.symm
    _ =
        (N.primeFactors.filter (fun p => 2 < p ∧ p < Z)).prod
            SingularSeries.liuCorrectionFactor *
          (S1SieveProductLowerOmittedPrimes N Z).prod
            SingularSeries.liuCorrectionFactor := by rw [hsmallSet, hlargeSet]

private theorem S1SieveProductLower_omittedPrimeProduct_dvd
    (N Z : ℕ) :
    (S1SieveProductLowerOmittedPrimes N Z).prod id ∣ N := by
  have hsubset : S1SieveProductLowerOmittedPrimes N Z ⊆ N.primeFactors :=
    Finset.filter_subset _ _
  exact (Finset.prod_dvd_prod_of_subset _ _ id hsubset).trans
    (Nat.prod_primeFactors_dvd N)

private theorem S1SieveProductLower_pow_card_le_omittedPrimeProduct
    (N Z : ℕ) :
    Z ^ (S1SieveProductLowerOmittedPrimes N Z).card ≤
      (S1SieveProductLowerOmittedPrimes N Z).prod id := by
  classical
  calc
    Z ^ (S1SieveProductLowerOmittedPrimes N Z).card =
        (S1SieveProductLowerOmittedPrimes N Z).prod (fun _ => Z) := by
          rw [← Finset.prod_const]
    _ ≤ (S1SieveProductLowerOmittedPrimes N Z).prod id := by
          apply Finset.prod_le_prod
          · intro p hp
            exact Nat.zero_le Z
          · intro p hp
            exact (Finset.mem_filter.mp hp).2.2

private theorem S1SieveProductLower_omittedPrimeCard_le_eighteen
    {N Z : ℕ} (hN : 0 < N) (hZ : 2 ≤ Z) (hNZ : N ≤ Z ^ 18) :
    (S1SieveProductLowerOmittedPrimes N Z).card ≤ 18 := by
  by_contra hcard
  have hcard19 : 19 ≤ (S1SieveProductLowerOmittedPrimes N Z).card := by omega
  have hprodLe : (S1SieveProductLowerOmittedPrimes N Z).prod id ≤ N :=
    Nat.le_of_dvd hN (S1SieveProductLower_omittedPrimeProduct_dvd N Z)
  have hpow19 :
      Z ^ 19 ≤ Z ^ (S1SieveProductLowerOmittedPrimes N Z).card :=
    Nat.pow_le_pow_right (by omega) hcard19
  have hpowProd :
      Z ^ (S1SieveProductLowerOmittedPrimes N Z).card ≤
        (S1SieveProductLowerOmittedPrimes N Z).prod id :=
    S1SieveProductLower_pow_card_le_omittedPrimeProduct N Z
  have hlt : Z ^ 18 < Z ^ 19 := by
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hle : Z ^ 19 ≤ Z ^ 18 := by
    exact le_trans hpow19 (le_trans hpowProd (le_trans hprodLe hNZ))
  exact (not_le_of_gt hlt) hle

private theorem S1SieveProductLower_correctionFactor_le_exp
    {p Z : ℕ} (hp2 : 2 < p) (hZ : 3 ≤ Z) (hZp : Z ≤ p) :
    SingularSeries.liuCorrectionFactor p ≤
      Real.exp (1 / ((Z - 2 : ℕ) : ℝ)) := by
  have hp2R : (2 : ℝ) < p := by exact_mod_cast hp2
  have hp2' : 0 < (p : ℝ) - 2 := by linarith
  have hZ2 : 2 ≤ Z := by omega
  have hZ2' : 0 < ((Z - 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < Z - 2 by omega)
  have hden :
      ((Z - 2 : ℕ) : ℝ) ≤ (p : ℝ) - 2 := by
    have hcast : ((Z - 2 : ℕ) : ℝ) = (Z : ℝ) - 2 := by
      simpa using (Nat.cast_sub hZ2 : ((Z - 2 : ℕ) : ℝ) = (Z : ℝ) - (2 : ℝ))
    have hpCast : (Z : ℝ) ≤ p := by exact_mod_cast hZp
    rw [hcast]
    linarith
  have hrecip :
      1 / ((p : ℝ) - 2) ≤ 1 / ((Z - 2 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hZ2' hden
  have hfactor :
      SingularSeries.liuCorrectionFactor p = 1 + 1 / ((p : ℝ) - 2) := by
    unfold SingularSeries.liuCorrectionFactor
    have hp2ne : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp [hp2ne]
    ring
  calc
    SingularSeries.liuCorrectionFactor p = 1 + 1 / ((p : ℝ) - 2) := hfactor
    _ ≤ Real.exp (1 / ((p : ℝ) - 2)) := by
          simpa [add_comm] using Real.add_one_le_exp (1 / ((p : ℝ) - 2))
    _ ≤ Real.exp (1 / ((Z - 2 : ℕ) : ℝ)) := Real.exp_le_exp.mpr hrecip

private theorem S1SieveProductLower_omittedCorrection_le_exp
    {N Z : ℕ} (hZ : 3 ≤ Z) :
    S1SieveProductLowerOmittedCorrection N Z ≤
      Real.exp (((S1SieveProductLowerOmittedPrimes N Z).card : ℝ) / ((Z - 2 : ℕ) : ℝ)) := by
  classical
  calc
    S1SieveProductLowerOmittedCorrection N Z ≤
        (S1SieveProductLowerOmittedPrimes N Z).prod
          (fun _ => Real.exp (1 / ((Z - 2 : ℕ) : ℝ))) := by
      unfold S1SieveProductLowerOmittedCorrection
      apply Finset.prod_le_prod
      · intro p hp
        exact (SingularSeries.liuCorrectionFactor_pos (Finset.mem_filter.mp hp).2.1).le
      · intro p hp
        exact S1SieveProductLower_correctionFactor_le_exp
          (Finset.mem_filter.mp hp).2.1 hZ (Finset.mem_filter.mp hp).2.2
    _ = Real.exp
        (∑ _p ∈ S1SieveProductLowerOmittedPrimes N Z, (1 / ((Z - 2 : ℕ) : ℝ) : ℝ)) := by
          rw [Real.exp_sum]
    _ = Real.exp (((S1SieveProductLowerOmittedPrimes N Z).card : ℝ) /
          ((Z - 2 : ℕ) : ℝ)) := by
          simp [div_eq_mul_inv]

private theorem S1SieveProductLower_exp_eighteen_div_le_one_add
    {δ : ℝ} (hδ : 0 < δ) {Z : ℕ}
    (hZ : 3 + 18 / Real.log (1 + δ) ≤ (Z : ℝ)) :
    Real.exp (18 / ((Z - 2 : ℕ) : ℝ)) ≤ 1 + δ := by
  have hlogPos : 0 < Real.log (1 + δ) := by
    apply Real.log_pos
    linarith
  have htailNonneg : 0 ≤ 18 / Real.log (1 + δ) := by positivity
  have hZ3 : (3 : ℝ) ≤ Z := by nlinarith
  have hZ3Nat : 3 ≤ Z := by exact_mod_cast hZ3
  have hZ2 : 2 ≤ Z := by omega
  have hZ2Pos : 0 < ((Z - 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < Z - 2 by omega)
  have hcast : ((Z - 2 : ℕ) : ℝ) = (Z : ℝ) - 2 := by
    simpa using (Nat.cast_sub hZ2 : ((Z - 2 : ℕ) : ℝ) = (Z : ℝ) - (2 : ℝ))
  have hden :
      18 / Real.log (1 + δ) ≤ ((Z - 2 : ℕ) : ℝ) := by
    rw [hcast]
    linarith
  have hdiv : 18 / ((Z - 2 : ℕ) : ℝ) ≤ Real.log (1 + δ) := by
    have hmul := mul_le_mul_of_nonneg_right hden hlogPos.le
    have hlogNe : Real.log (1 + δ) ≠ 0 := ne_of_gt hlogPos
    have hmain :
        18 ≤ ((Z - 2 : ℕ) : ℝ) * Real.log (1 + δ) := by
      simpa [div_eq_mul_inv, hlogNe, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact (div_le_iff₀ hZ2Pos).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
  calc
    Real.exp (18 / ((Z - 2 : ℕ) : ℝ)) ≤ Real.exp (Real.log (1 + δ)) :=
      Real.exp_le_exp.mpr hdiv
    _ = 1 + δ := by
      rw [Real.exp_log]
      linarith

private theorem S1SieveProductLower_omittedCorrection_le_one_add
    {N Z : ℕ} (hN : 0 < N) (hZ : 3 ≤ Z) (hNZ : N ≤ Z ^ 18)
    {δ : ℝ} (hδ : 0 < δ)
    (hcut : 3 + 18 / Real.log (1 + δ) ≤ (Z : ℝ)) :
    S1SieveProductLowerOmittedCorrection N Z ≤ 1 + δ := by
  have hcard :
      (S1SieveProductLowerOmittedPrimes N Z).card ≤ 18 :=
    S1SieveProductLower_omittedPrimeCard_le_eighteen hN (by omega) hNZ
  have hdenPos : 0 < ((Z - 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < Z - 2 by omega)
  have hdiv :
      (((S1SieveProductLowerOmittedPrimes N Z).card : ℝ) / ((Z - 2 : ℕ) : ℝ)) ≤
        18 / ((Z - 2 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hdenPos.le
  calc
    S1SieveProductLowerOmittedCorrection N Z ≤
        Real.exp (((S1SieveProductLowerOmittedPrimes N Z).card : ℝ) /
          ((Z - 2 : ℕ) : ℝ)) :=
      S1SieveProductLower_omittedCorrection_le_exp hZ
    _ ≤ Real.exp (18 / ((Z - 2 : ℕ) : ℝ)) := Real.exp_le_exp.mpr hdiv
    _ ≤ 1 + δ := S1SieveProductLower_exp_eighteen_div_le_one_add hδ hcut

private theorem S1SieveProductLower_correctionTruncated_ge_one_sub
    {N Z : ℕ} (hN : 0 < N) (hZ : 3 ≤ Z) (hNZ : N ≤ Z ^ 18)
    {δ : ℝ} (hδ : 0 < δ)
    (hcut : 3 + 18 / Real.log (1 + δ) ≤ (Z : ℝ)) :
    (1 - δ) * SingularSeries.liuCorrection N ≤
      SingularSeries.liuCorrectionTruncated N (Z - 1) := by
  let T := S1SieveProductLowerOmittedCorrection N Z
  have hTpos : 0 < T := by
    unfold T S1SieveProductLowerOmittedCorrection
    exact Finset.prod_pos fun p hp =>
      SingularSeries.liuCorrectionFactor_pos (Finset.mem_filter.mp hp).2.1
  have hTle : T ≤ 1 + δ :=
    S1SieveProductLower_omittedCorrection_le_one_add hN hZ hNZ hδ hcut
  have hInv₁ : 1 - δ ≤ (1 + δ)⁻¹ := by
    have h1δ : 0 < 1 + δ := by linarith
    have hmul : (1 - δ) * (1 + δ) ≤ 1 := by
      nlinarith [sq_nonneg δ]
    simpa [one_div] using (le_div_iff₀ h1δ).2 hmul
  have hInv₂ : (1 + δ)⁻¹ ≤ T⁻¹ := by
    have h1δ : 0 < 1 + δ := by linarith
    exact (inv_le_inv₀ h1δ hTpos).2 hTle
  have hInv : 1 - δ ≤ T⁻¹ := hInv₁.trans hInv₂
  have hCorrNonneg : 0 ≤ SingularSeries.liuCorrection N := (SingularSeries.liuCorrection_pos N).le
  have hmul :
      (1 - δ) * SingularSeries.liuCorrection N ≤
        SingularSeries.liuCorrection N * T⁻¹ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hInv hCorrNonneg
  have hdecomp :
      SingularSeries.liuCorrection N =
        SingularSeries.liuCorrectionTruncated N (Z - 1) * T := by
    simpa [T] using
      S1SieveProductLower_liuCorrection_eq_truncated_mul_omitted hN (by omega)
  have hrewrite :
      SingularSeries.liuCorrection N * T⁻¹ =
        SingularSeries.liuCorrectionTruncated N (Z - 1) := by
    rw [hdecomp]
    field_simp [hTpos.ne']
  calc
    (1 - δ) * SingularSeries.liuCorrection N ≤
        SingularSeries.liuCorrection N * T⁻¹ := hmul
    _ = SingularSeries.liuCorrectionTruncated N (Z - 1) := hrewrite

private theorem S1SieveProductLower_truncated_ge_one_sub_liuSingularSeries
    {N Z : ℕ} (hN : 0 < N) (hZ : 3 ≤ Z) (hNZ : N ≤ Z ^ 18)
    {δ : ℝ} (hδ : 0 < δ)
    (hcut : 3 + 18 / Real.log (1 + δ) ≤ (Z : ℝ)) :
    (1 - δ) * SingularSeries.liuSingularSeries N ≤
      SingularSeries.liuSingularSeriesTruncated N (Z - 1) := by
  have hCorr :
      (1 - δ) * SingularSeries.liuCorrection N ≤
        SingularSeries.liuCorrectionTruncated N (Z - 1) :=
    S1SieveProductLower_correctionTruncated_ge_one_sub hN hZ hNZ hδ hcut
  calc
    (1 - δ) * SingularSeries.liuSingularSeries N =
        ((1 - δ) * SingularSeries.liuCorrection N) * SingularSeries.liuUniversalProduct := by
          rw [SingularSeries.liuSingularSeries]
          ring
    _ ≤ SingularSeries.liuCorrectionTruncated N (Z - 1) *
          SingularSeries.liuUniversalProduct := by
          exact mul_le_mul_of_nonneg_right hCorr SingularSeries.liuUniversalProduct_nonneg
    _ ≤ SingularSeries.liuCorrectionTruncated N (Z - 1) *
          SingularSeries.liuUniversalProductTruncated (Z - 1) := by
          exact mul_le_mul_of_nonneg_left
            (SingularSeries.liuUniversalProduct_le_truncated (Z - 1))
            (SingularSeries.liuCorrectionTruncated_pos N (Z - 1)).le
    _ = SingularSeries.liuSingularSeriesTruncated N (Z - 1) := by
          rw [SingularSeries.liuSingularSeriesTruncated_factorization]

private theorem S1SieveProductLower_nat_le_ceil_pow
    {N : ℕ} {z : ℝ} (hz : (N : ℝ) ^ (1 / 18 : ℝ) ≤ z) :
    N ≤ Nat.ceil z ^ 18 := by
  have hceil : (N : ℝ) ^ (1 / 18 : ℝ) ≤ (Nat.ceil z : ℝ) := hz.trans (Nat.le_ceil z)
  have hpow :
      ((N : ℝ) ^ (1 / 18 : ℝ)) ^ 18 ≤ (Nat.ceil z : ℝ) ^ 18 := by
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _) hceil 18
  have hmain : (N : ℝ) ≤ (Nat.ceil z : ℝ) ^ 18 := by
    calc
      (N : ℝ) = ((N : ℝ) ^ (1 / 18 : ℝ)) ^ 18 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
        norm_num
      _ ≤ (Nat.ceil z : ℝ) ^ 18 := hpow
  exact_mod_cast hmain

private theorem S1SieveProductLower_goldbachSieveProduct_nonneg
    {N Z : ℕ} (hEven : Even N) :
    0 ≤ MertensTheorem.goldbachSieveProduct N Z := by
  unfold MertensTheorem.goldbachSieveProduct
  apply Finset.prod_nonneg
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpPrime, hpNotDvd⟩
  have hpNeTwo : p ≠ 2 := by
    intro hp2
    have h2dvd : 2 ∣ N := by
      rcases hEven with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk]
      omega
    exact hpNotDvd (by simpa [hp2] using h2dvd)
  have hp3 : 3 ≤ p := by
    have hp2le : 2 ≤ p := hpPrime.two_le
    omega
  have hfrac : 1 / ((p : ℝ) - 1) ≤ 1 := by
    have hpos : 0 < (p : ℝ) - 1 := by
      have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    rw [div_le_iff₀ hpos]
    have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  linarith

theorem goldbachS1PrimeProduct_log_ge_liuSingularSeries
    (η : ℝ) (hη : 0 < η) (_hη1 : η < 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N → ∀ z : ℝ,
      (N : ℝ) ^ (1 / 18 : ℝ) ≤ z →
        2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - η) *
            SingularSeries.liuSingularSeries N ≤
          MertensTheorem.goldbachSieveProduct N (Nat.ceil z) * Real.log z := by
  let δ : ℝ := η / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδlt1 : δ < 1 := by
    dsimp [δ]
    nlinarith
  have hOneSubδ : 0 ≤ 1 - δ := by linarith
  obtain ⟨C, hC⟩ := MertensTheorem.sieve_product_asymptotic
  let tailThreshold : ℝ := 3 + 18 / Real.log (1 + δ)
  let errThreshold : ℝ :=
    2 * Real.exp (|C| / (δ * Real.exp (-Real.eulerMascheroniConstant)))
  let Z₀ : ℕ := Nat.ceil (max tailThreshold errThreshold)
  let N₀ : ℕ := max 4 (Z₀ ^ 18)
  refine ⟨N₀, le_max_left _ _, ?_⟩
  intro N hNN₀ hEven z hz
  let Z : ℕ := Nat.ceil z
  have hN4 : 4 ≤ N := (le_max_left 4 (Z₀ ^ 18)).trans hNN₀
  have hNpos : 0 < N := by omega
  have hZ₀Pow : Z₀ ^ 18 ≤ N := (le_max_right 4 (Z₀ ^ 18)).trans hNN₀
  have hZ₀leRoot : (Z₀ : ℝ) ≤ (N : ℝ) ^ (1 / 18 : ℝ) := by
    have hcast : (Z₀ : ℝ) ^ 18 ≤ (N : ℝ) := by
      exact_mod_cast hZ₀Pow
    have hroot :=
      Real.rpow_le_rpow (by positivity : 0 ≤ (Z₀ : ℝ) ^ 18) hcast
        (by norm_num : 0 ≤ (1 / 18 : ℝ))
    calc
      (Z₀ : ℝ) = ((Z₀ : ℝ) ^ 18) ^ (1 / 18 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Z₀)]
        norm_num
      _ ≤ (N : ℝ) ^ (1 / 18 : ℝ) := hroot
  have hZ₀lez : (Z₀ : ℝ) ≤ z := hZ₀leRoot.trans hz
  have hZ₀leZ : Z₀ ≤ Z := by
    dsimp [Z]
    exact_mod_cast (hZ₀lez.trans (Nat.le_ceil z))
  have hZ₀Cast : (Z₀ : ℝ) ≤ Z := by exact_mod_cast hZ₀leZ
  have hcut : max tailThreshold errThreshold ≤ (Z : ℝ) := by
    exact (Nat.le_ceil (max tailThreshold errThreshold)).trans hZ₀Cast
  have htailCut : tailThreshold ≤ (Z : ℝ) := (le_max_left _ _).trans hcut
  have herrCut : errThreshold ≤ (Z : ℝ) := (le_max_right _ _).trans hcut
  have hlogTailPos : 0 < Real.log (1 + δ) := by
    apply Real.log_pos
    linarith
  have htailNonneg : 0 ≤ 18 / Real.log (1 + δ) := by positivity
  have hZ3r : (3 : ℝ) ≤ Z := by
    have htailCut' : 3 + 18 / Real.log (1 + δ) ≤ (Z : ℝ) := by
      simpa [tailThreshold] using htailCut
    nlinarith
  have hZ3 : 3 ≤ Z := by exact_mod_cast hZ3r
  have hNZ : N ≤ Z ^ 18 := by
    dsimp [Z]
    exact S1SieveProductLower_nat_le_ceil_pow hz
  have htruncLower :
      (1 - δ) * SingularSeries.liuSingularSeries N ≤
        SingularSeries.liuSingularSeriesTruncated N (Z - 1) :=
    S1SieveProductLower_truncated_ge_one_sub_liuSingularSeries hNpos hZ3 hNZ hδ <|
      by simpa [tailThreshold] using htailCut
  have hlogPos : 0 < Real.log ((Z - 1 : ℕ) : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < Z - 1 by omega))
  have hErr :
      |C| / Real.log ((Z - 1 : ℕ) : ℝ) ≤
        δ * Real.exp (-Real.eulerMascheroniConstant) :=
    S1SieveProductLower_absConst_div_log_le hδ hZ3 <| by
      dsimp [errThreshold] at herrCut
      exact herrCut
  have hsieveAbs :
      |MertensTheorem.goldbachSieveProduct N Z -
          SingularSeries.singularSeriesTruncated N (Z - 1) *
            Real.exp (-Real.eulerMascheroniConstant) /
              Real.log ((Z - 1 : ℕ) : ℝ)| ≤
        C * SingularSeries.singularSeriesTruncated N (Z - 1) /
          (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2 :=
    hC N Z hZ3 hEven hN4
  have hsieveAbs' :
      |MertensTheorem.goldbachSieveProduct N Z -
          SingularSeries.singularSeriesTruncated N (Z - 1) *
            Real.exp (-Real.eulerMascheroniConstant) /
              Real.log ((Z - 1 : ℕ) : ℝ)| ≤
        |C| * SingularSeries.singularSeriesTruncated N (Z - 1) /
          (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2 := by
    calc
      |MertensTheorem.goldbachSieveProduct N Z -
          SingularSeries.singularSeriesTruncated N (Z - 1) *
            Real.exp (-Real.eulerMascheroniConstant) /
              Real.log ((Z - 1 : ℕ) : ℝ)|
        ≤ C * SingularSeries.singularSeriesTruncated N (Z - 1) /
            (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2 := hsieveAbs
      _ ≤ |C| * SingularSeries.singularSeriesTruncated N (Z - 1) /
            (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2 := by
          have hSpos :
              0 < SingularSeries.singularSeriesTruncated N (Z - 1) :=
            SingularSeries.singularSeriesTruncated_pos N (Z - 1) (by omega)
          have hterm :
              0 ≤ SingularSeries.singularSeriesTruncated N (Z - 1) /
                (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2 := by
            exact div_nonneg hSpos.le (sq_nonneg _)
          have hCabs :
              C * (SingularSeries.singularSeriesTruncated N (Z - 1) /
                    (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2) ≤
                |C| * (SingularSeries.singularSeriesTruncated N (Z - 1) /
                    (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) hterm
          calc
            C * SingularSeries.singularSeriesTruncated N (Z - 1) /
                (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2
              = C * (SingularSeries.singularSeriesTruncated N (Z - 1) /
                  (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2) := by ring
            _ ≤ |C| * (SingularSeries.singularSeriesTruncated N (Z - 1) /
                  (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2) := hCabs
            _ = |C| * SingularSeries.singularSeriesTruncated N (Z - 1) /
                  (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2 := by ring
  have hlegacy :
      SingularSeries.singularSeriesTruncated N (Z - 1) =
        2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) :=
    SingularSeries.singularSeriesTruncated_eq_two_mul_liuSingularSeriesTruncated
      N (Z - 1) hEven (by omega)
  have hLowerProduct :
      2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) *
          (Real.exp (-Real.eulerMascheroniConstant) /
              Real.log ((Z - 1 : ℕ) : ℝ) -
            |C| / (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2) ≤
        MertensTheorem.goldbachSieveProduct N Z := by
    have hmain :
        SingularSeries.singularSeriesTruncated N (Z - 1) *
            Real.exp (-Real.eulerMascheroniConstant) /
              Real.log ((Z - 1 : ℕ) : ℝ) -
          |C| * SingularSeries.singularSeriesTruncated N (Z - 1) /
            (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2 ≤
        MertensTheorem.goldbachSieveProduct N Z := by
      have hsub :
          -(|C| * SingularSeries.singularSeriesTruncated N (Z - 1) /
              (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2) ≤
            MertensTheorem.goldbachSieveProduct N Z -
              SingularSeries.singularSeriesTruncated N (Z - 1) *
                Real.exp (-Real.eulerMascheroniConstant) /
                  Real.log ((Z - 1 : ℕ) : ℝ) := (abs_le.mp hsieveAbs').1
      linarith
    rw [hlegacy] at hmain
    have hrew :
        (2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1)) *
            Real.exp (-Real.eulerMascheroniConstant) /
              Real.log ((Z - 1 : ℕ) : ℝ) -
          |C| * (2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1)) /
            (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2 =
        2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) *
          (Real.exp (-Real.eulerMascheroniConstant) /
              Real.log ((Z - 1 : ℕ) : ℝ) -
            |C| / (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2) := by
      ring
    simpa [hrew] using hmain
  have hMulLog :
      2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) *
          (Real.exp (-Real.eulerMascheroniConstant) -
            |C| / Real.log ((Z - 1 : ℕ) : ℝ)) ≤
        MertensTheorem.goldbachSieveProduct N Z * Real.log ((Z - 1 : ℕ) : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hLowerProduct hlogPos.le
    calc
      2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) *
          (Real.exp (-Real.eulerMascheroniConstant) -
            |C| / Real.log ((Z - 1 : ℕ) : ℝ))
        = 2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) *
            (Real.exp (-Real.eulerMascheroniConstant) /
                Real.log ((Z - 1 : ℕ) : ℝ) -
              |C| / (Real.log ((Z - 1 : ℕ) : ℝ)) ^ 2) *
            Real.log ((Z - 1 : ℕ) : ℝ) := by
              field_simp [hlogPos.ne']
      _ ≤ MertensTheorem.goldbachSieveProduct N Z * Real.log ((Z - 1 : ℕ) : ℝ) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hCoeffLower :
      Real.exp (-Real.eulerMascheroniConstant) * (1 - δ) ≤
        Real.exp (-Real.eulerMascheroniConstant) -
          |C| / Real.log ((Z - 1 : ℕ) : ℝ) := by
    linarith
  have hTruncNonneg :
      0 ≤ 2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) := by
    have hTruncPos : 0 < SingularSeries.liuSingularSeriesTruncated N (Z - 1) :=
      SingularSeries.liuSingularSeriesTruncated_pos N (Z - 1)
    positivity
  have hMainLower :
      2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - δ) *
          SingularSeries.liuSingularSeriesTruncated N (Z - 1) ≤
        MertensTheorem.goldbachSieveProduct N Z * Real.log ((Z - 1 : ℕ) : ℝ) := by
    calc
      2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - δ) *
          SingularSeries.liuSingularSeriesTruncated N (Z - 1)
        = 2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) *
            (Real.exp (-Real.eulerMascheroniConstant) * (1 - δ)) := by
              ring
      _ ≤ 2 * SingularSeries.liuSingularSeriesTruncated N (Z - 1) *
            (Real.exp (-Real.eulerMascheroniConstant) -
              |C| / Real.log ((Z - 1 : ℕ) : ℝ)) := by
              gcongr
      _ ≤ MertensTheorem.goldbachSieveProduct N Z * Real.log ((Z - 1 : ℕ) : ℝ) := hMulLog
  have hCoeffNonneg :
      0 ≤ 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - δ) := by
    exact mul_nonneg (by positivity) hOneSubδ
  have hStrong :
      2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - δ) ^ 2 *
          SingularSeries.liuSingularSeries N ≤
        MertensTheorem.goldbachSieveProduct N Z * Real.log ((Z - 1 : ℕ) : ℝ) := by
    calc
      2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - δ) ^ 2 *
          SingularSeries.liuSingularSeries N
        = (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - δ)) *
            ((1 - δ) * SingularSeries.liuSingularSeries N) := by
              ring
      _ ≤ (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - δ)) *
            SingularSeries.liuSingularSeriesTruncated N (Z - 1) := by
              exact mul_le_mul_of_nonneg_left htruncLower hCoeffNonneg
      _ = 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - δ) *
            SingularSeries.liuSingularSeriesTruncated N (Z - 1) := by
              ring
      _ ≤ MertensTheorem.goldbachSieveProduct N Z * Real.log ((Z - 1 : ℕ) : ℝ) := hMainLower
  have hEtaCoeff :
      1 - η ≤ (1 - δ) ^ 2 := by
    dsimp [δ]
    nlinarith [sq_nonneg η]
  have hEtaToDelta :
      2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - η) *
          SingularSeries.liuSingularSeries N ≤
        2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - δ) ^ 2 *
          SingularSeries.liuSingularSeries N := by
    have hbase : 0 ≤ 2 * Real.exp (-Real.eulerMascheroniConstant) := by positivity
    have hcoef :
        2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - η) ≤
          2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - δ) ^ 2 := by
      gcongr
    exact mul_le_mul_of_nonneg_right hcoef (SingularSeries.liuSingularSeries_pos N).le
  have hVnonneg : 0 ≤ MertensTheorem.goldbachSieveProduct N Z :=
    S1SieveProductLower_goldbachSieveProduct_nonneg hEven
  have hargPos : 0 < ((Z - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < Z - 1 by omega)
  have hargLt : ((Z - 1 : ℕ) : ℝ) < z := by
    have hzNonneg : 0 ≤ z := le_trans (Real.rpow_nonneg (Nat.cast_nonneg N) _) hz
    have hceilLt : (Z : ℝ) < z + 1 := by
      dsimp [Z]
      exact Nat.ceil_lt_add_one hzNonneg
    have hcast : ((Z - 1 : ℕ) : ℝ) = (Z : ℝ) - 1 := by
      simpa using (Nat.cast_sub (by omega : 1 ≤ Z) :
        ((Z - 1 : ℕ) : ℝ) = (Z : ℝ) - ((1 : ℕ) : ℝ))
    rw [hcast]
    linarith
  have hlogMono :
      Real.log ((Z - 1 : ℕ) : ℝ) ≤ Real.log z := by
    exact Real.log_le_log hargPos hargLt.le
  calc
    2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - η) *
        SingularSeries.liuSingularSeries N
      ≤ 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - δ) ^ 2 *
          SingularSeries.liuSingularSeries N := hEtaToDelta
    _ ≤ MertensTheorem.goldbachSieveProduct N Z * Real.log ((Z - 1 : ℕ) : ℝ) := hStrong
    _ ≤ MertensTheorem.goldbachSieveProduct N Z * Real.log z := by
      exact mul_le_mul_of_nonneg_left hlogMono hVnonneg

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig