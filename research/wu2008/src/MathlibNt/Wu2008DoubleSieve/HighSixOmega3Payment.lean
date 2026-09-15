import MathlibNt.Wu2008DoubleSieve.HighSixOmega3Switching

namespace Wu2008DoubleSieve.HighSix.Omega3Upper
open Finset Real Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries

/-- A support comparison, not a source-box specialization. -/
theorem theta_lower {N : ℕ} {δ : ℝ} (hN : 4 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    2*liuUniversalProduct*(N : ℝ)/log N^2 * boxConvolutionReciprocalMass (W N) ≤
      B6 N δ := by
  apply boxTheta_lower_of_support (W N) hN (fun _ hp => support_pos hp)
  intro p hp
  rw [support] at hp
  have hg := support_geometry (by omega) hδ hδhi hp
  exact ⟨hg.2.2.2.1,hg.2.2.2.2.1⟩

/-- Every fixed power error is paid before N, with the full reciprocal mass. -/
theorem power_mass_paid {δ ε C ρ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) (hC : 0 < C) (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      (C*((N : ℝ)/(N : ℝ)^ρ))*boxConvolutionReciprocalMass (W N) ≤ ε*B6 N δ := by
  have hU := liuUniversalProduct_pos
  obtain ⟨T,hT⟩ := eventually_atTop.mp (box_eventually_log_power_budget 2
    (show 0 < C/(2*ε*liuUniversalProduct) by positivity) hρ)
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN
  have hN4 : 4 ≤ N := by omega
  have hpay := hT N (by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcoef : C*((N : ℝ)/(N : ℝ)^ρ) ≤
      ε*(2*liuUniversalProduct*(N : ℝ)/log N^2) := by
    calc
      _ ≤ C*((N : ℝ)/((C/(2*ε*liuUniversalProduct))*log (N : ℝ)^2)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity) hpay) hC.le
      _ = _ := by field_simp
  have hm : 0 ≤ boxConvolutionReciprocalMass (W N) :=
    sum_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ (ε*(2*liuUniversalProduct*(N : ℝ)/log N^2))*boxConvolutionReciprocalMass (W N) :=
      mul_le_mul_of_nonneg_right hcoef hm
    _ = ε*((2*liuUniversalProduct*(N : ℝ)/log N^2)*boxConvolutionReciprocalMass (W N)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (theta_lower hN4 hδ hδhi) hε.le

/-- The bad-d test keeps the original labels, including repeated cofactors. -/
theorem badD_bound {N : ℕ} {δ : ℝ} (hN : 4 ≤ N) (he : Even N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    omega3BadDCount N δ s S (W N) ≤
      (25^4*((N : ℝ)/(N : ℝ)^(1/25 : ℝ)))*boxConvolutionReciprocalMass (W N) := by
  have hl (p : ℕ) (hp : p ∈ boxConvolutionSupport (W N)) :
      (N : ℝ)^(1/25 : ℝ) ≤ wuLocalCutoff N δ p S := by
    rw [support] at hp
    exact inner_lower_cutoff (by omega) hδ hδhi hp
  have hf := omega3_badDCount_le_reciprocal_mass (s := s) (t := S) (η := 1/25)
    (W N) hN he (by norm_num)
    (fun p hp => by
      rw [support] at hp
      exact ⟨(support_geometry (by omega) hδ hδhi hp).1,
        (support_geometry (by omega) hδ hδhi hp).2.1⟩) hl (by
      intro p hp q hq
      rw [support] at hp
      have hpp := (mem_primeWindow.mp hp).1
      have hqp : q = p := by simpa only [hpp.primeFactors, mem_singleton] using hq
      subst q
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      exact (rpow_le_rpow_of_exponent_le hNr (by norm_num [left])).trans
        (mem_primeWindow.mp hp).2.2.1)
  norm_num at hf ⊢
  exact hf

/-- Exceptional prime outputs are counted once per full ordered label. -/
theorem exceptional_bound {N : ℕ} {δ : ℝ} (hN : 4 ≤ N) (he : Even N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    omega3ExceptionalOutputCount N δ s S (W N) ≤
      (4*25^3*((N : ℝ)/(N : ℝ)^δ))*boxConvolutionReciprocalMass (W N) := by
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by positivity
  have hf := omega3_exceptional_count_le (s := s) (t := S) (η := 1/25)
    (W N) hN he (by norm_num) (fun p hp => by
      rw [support] at hp
      exact inner_lower_cutoff hN2 hδ hδhi hp)
  have hmass : (∑ p ∈ boxConvolutionSupport (W N), (convolutionCoeff (W N) p : ℝ)) ≤
      (N : ℝ)^(1/2-δ)*boxConvolutionReciprocalMass (W N) := by
    unfold boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpP : p ∈ P N := (support N) ▸ hp
    have hg := support_geometry hN2 hδ hδhi hpP
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hg.1
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hp0).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hg.2.2.1
      (Nat.cast_nonneg (convolutionCoeff (W N) p))
  have hrec : 0 ≤ boxConvolutionReciprocalMass (W N) :=
    sum_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hpow : sqrt (N : ℝ)*(N : ℝ)^(1/2-δ) = (N : ℝ)/(N : ℝ)^δ := by
    rw [sqrt_eq_rpow, ← rpow_add hNr]
    calc
      _ = (N : ℝ)^(1-δ) := by congr 1; ring
      _ = _ := by rw [rpow_sub hNr,rpow_one]
  apply hf.trans
  calc
    _ = (25^3*((omega3ExceptionalOutputs N δ).card : ℝ))*
        ∑ p ∈ boxConvolutionSupport (W N), (convolutionCoeff (W N) p : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intros
      norm_num
      ring
    _ ≤ (25^3*(4*sqrt (N : ℝ)))*((N : ℝ)^(1/2-δ)*boxConvolutionReciprocalMass (W N)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (omega3ExceptionalOutputs_card_le (by omega) hδ.le) (by positivity)) hmass
        (sum_nonneg fun _ _ => Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← hpow]; ring

/-- High-prime switching with both actual finite exceptions paid internally. -/
theorem switching_theta_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      O3 N δ ≤ omega3SwitchedSiftedCount N δ s S
        (sqrt ((N : ℝ)^(1/2-δ))) (W N)+ε*B6 N δ := by
  obtain ⟨T1,hT14,hT1⟩ := power_mass_paid hδ hδhi (half_pos hε)
    (show (0 : ℝ) < 25^4 by norm_num) (show (0 : ℝ) < 1/25 by norm_num)
  obtain ⟨T2,_,hT2⟩ := power_mass_paid hδ hδhi (half_pos hε)
    (show (0 : ℝ) < 4*25^3 by norm_num) hδ
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hN4 : 4 ≤ N := by omega
  have hd := (badD_bound hN4 he hδ hδhi).trans (hT1 N (by omega))
  have hx := (exceptional_bound hN4 he hδ hδhi).trans (hT2 N (by omega))
  have hf := switching_finite (δ := δ) hN4 he
  linarith

/-- The full 480-mass bound pays switching on the final count scale. -/
theorem switching_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      O3 N δ ≤ omega3SwitchedSiftedCount N δ s S
        (sqrt ((N : ℝ)^(1/2-δ))) (W N)+ε*truncatedSixthMassScale N := by
  obtain ⟨T1,hT14,hT1⟩ := switching_theta_paid hδ hδhi (show 0 < ε/480 by positivity)
  obtain ⟨T2,_,hT2⟩ := B6_total_mass hδ hδhi
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hf := hT1 N (by omega) he
  have hm := mul_le_mul_of_nonneg_left (hT2 N (by omega) he).2 (show 0 ≤ ε/480 by positivity)
  nlinarith

/-- An unconditional actual-X endpoint. R1 and R2 remain literal finite
remainders; this is not the target integral estimate with assumptions. -/
theorem O3_actualX_paid {δ ρ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      O3 N δ ≤ omega3SieveX N δ s S (W N) *
        (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
          wuSingularSeries N/log N) +
      omega3SieveR1 N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) δ s S
        (sqrt ((N : ℝ)^(1/2-δ))) (W N) +
      omega3SieveR2 N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) δ s S
        (sqrt ((N : ℝ)^(1/2-δ))) (W N) + ε*truncatedSixthMassScale N := by
  obtain ⟨T1,hT14,hT1⟩ := switching_paid hδ hδhi hε
  obtain ⟨T2,_,hT2⟩ := switched_density hδ hδhi hρ
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hs := hT1 N (by omega) he
  have hd := hT2 N (by omega) he
  linarith

/-- Consume the proved negative integral and the actual high-prime producer.
O1, actual X, full-cofactor R1 and Euler R2 are deliberately still visible. -/
theorem count_actualX_paid {δ ρ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      2*C6 N ≤ O1 N δ-J*B6 N δ + omega3SieveX N δ s S (W N) *
        (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
          wuSingularSeries N/log N) +
      omega3SieveR1 N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) δ s S
        (sqrt ((N : ℝ)^(1/2-δ))) (W N) +
      omega3SieveR2 N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) δ s S
        (sqrt ((N : ℝ)^(1/2-δ))) (W N) + ε*truncatedSixthMassScale N := by
  obtain ⟨T1,hT14,hT1⟩ := count_integral_paid hδ hδhi (half_pos hε)
  obtain ⟨T2,_,hT2⟩ := O3_actualX_paid hδ hδhi hρ (half_pos hε)
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hc := hT1 N (by omega) he
  have ho := hT2 N (by omega) he
  linarith

end Wu2008DoubleSieve.HighSix.Omega3Upper
