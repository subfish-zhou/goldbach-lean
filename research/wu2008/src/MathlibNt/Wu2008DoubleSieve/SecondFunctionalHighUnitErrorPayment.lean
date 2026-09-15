import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSieveInstance
import MathlibNt.Wu2008DoubleSieve.Omega3R2Source

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitSieve
open Real Filter Finset

/-- The real closed small-output threshold and its exact power saving. -/
theorem source_small_power {N : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    let β := (1/2-δ)/2
    0 < β ∧ β < 1 ∧
      sqrt ((N : ℝ)^(1/2-δ)) = (N : ℝ)^β ∧
      0 ≤ sqrt ((N : ℝ)^(1/2-δ)) ∧ sqrt ((N : ℝ)^(1/2-δ)) < N ∧
      ∀ C : ℝ, C * sqrt ((N : ℝ)^(1/2-δ)) =
        C * N * log N ^ (0 : ℕ) / (N : ℝ)^(1-β) := by
  dsimp only
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpos : (0 : ℝ) < N := lt_trans zero_lt_one hNr
  have heq : sqrt ((N : ℝ)^(1/2-δ)) = (N : ℝ)^((1/2-δ)/2) := by
    rw [sqrt_eq_rpow, ← rpow_mul hpos.le]
    congr 1
    ring
  refine ⟨by linarith, by linarith, heq, sqrt_nonneg _, ?_, ?_⟩
  · rw [heq]
    simpa only [rpow_one] using
      rpow_lt_rpow_of_exponent_lt hNr (show (1/2-δ)/2 < 1 by linarith)
  · intro C
    rw [heq, pow_zero, mul_one, rpow_sub hpos, rpow_one]
    field_simp

/-- Both actual words pay R2 and the CLOSED small outputs, with internal half budgets.
The threshold precedes every source box and every mother parameter. -/
theorem mother_R2_closedSmall_payment (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ (T : ℕ) (hT : 4 ≤ T), ∀ (N : ℕ) (hN : T ≤ N),
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ) (hb : wuSourceBox k δ N i Δ V),
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let hN2 : 2 ≤ N := (show 2 ≤ 4 by omega).trans (hT.trans hN)
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ)^(1/2-δ)
      let D := ⌊Q⌋₊ + 1
      let Z := sqrt Q
      let R := fun d : ℕ => Q/d
      let a2 := fun _ : ℕ => 1/p.kappa2
      let a3 := fun _ : ℕ => 1/p.kappa3
      let b := fun _ : ℕ => 1/p.s
      let L20 := sourceFamily hN2 hδ hδhi hb
        (fun d => HighUnit.primePrefix20 (R d) (a2 d) (a3 d) (b d)) (Fin.last 3) b
      let L21 := sourceFamily hN2 hδ hδhi hb
        (fun d => HighUnit.primePrefix21 (R d) (a3 d) (b d)) (Fin.last 4) b
      let E := L20.R2 D Z + L21.R2 D Z
      let S := smallOutputMassReal N Z W (family20 N W R a2 a3 b) (Fin.last 3) b +
        smallOutputMassReal N Z W (family21 N W R a3 b) (Fin.last 4) b
      E ≤ (ε/2) * boxTheta N Q W ∧ S ≤ (ε/2) * boxTheta N Q W ∧
        E + S ≤ ε * boxTheta N Q W := by
  let η := wuLocalExponent k δ / 10
  let H := max 1 (1/η)
  let F := H^(k+5)
  let G := H^(k+6)
  let β := (1/2-δ)/2
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hH : 1 ≤ H := le_max_left _ _
  have hF : 0 < F := pow_pos (lt_of_lt_of_le zero_lt_one hH) _
  have hG : 0 < G := pow_pos (lt_of_lt_of_le zero_lt_one hH) _
  have hρ : 0 < 1-β := by dsimp [β]; linarith
  have heps : 0 < ε/2 := by positivity
  obtain ⟨C, hC, hEuler⟩ := LabelledPhysical.Family.R2_euler.{0}
  obtain ⟨T0, hT04, hT0⟩ := source_mother_small_pair k hδ hδhi
  obtain ⟨T1, _, hT1⟩ := omega3_absolute_power_log_relative k 5 hδ hδhi heps
    (show 0 < 4*C*F/log 2 by positivity) hη
  obtain ⟨T2, _, hT2⟩ := omega3_absolute_power_log_relative k 0 hδ hδhi heps
    (show 0 < 2*G by positivity) hρ
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T3, hT3⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  let T := max T0 (max T1 (max T2 T3))
  have hT4 : 4 ≤ T := hT04.trans (le_max_left _ _)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  have hN0 : T0 ≤ N := (le_max_left _ _).trans hN
  have hN1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2' : T2 ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN3 : T3 ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN4 : 4 ≤ N := hT4.trans hN
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog1 := hT3 N hN3
  have hgeom := omega3_source_sieve_geometry hN2 hδ hδhi
  have hpow := source_small_power hN2 hδ hδhi
  obtain ⟨_, hf20, hf21, hsmall, _⟩ := hT0 N hN0 i Δ V hb p hp hs
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ)^(1/2-δ)
  let D := ⌊Q⌋₊ + 1
  let Z := sqrt Q
  let R := fun d : ℕ => Q/d
  let a2 := fun _ : ℕ => 1/p.kappa2
  let a3 := fun _ : ℕ => 1/p.kappa3
  let b := fun _ : ℕ => 1/p.s
  let L20 := sourceFamily hN2 hδ hδhi hb
    (fun d => HighUnit.primePrefix20 (R d) (a2 d) (a3 d) (b d)) (Fin.last 3) b
  let L21 := sourceFamily hN2 hδ hδhi hb
    (fun d => HighUnit.primePrefix21 (R d) (a3 d) (b d)) (Fin.last 4) b
  have hmod : ∀ q ∈ omega3SieveModuli N D Z, q ≤ N := by
    intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hgeom.2.2.2.2.2.2.1
    dsimp only [D, Q] at hqd
    omega
  have hr20 := hEuler N (by omega) _ L20 D Z ((N : ℝ)^η) F
    hgeom.2.2.2.1 (rpow_pos_of_pos hNr _) hF.le hmod
    (fun c hc => (hf20.1 c hc).2) (fun e => (hf20.2 e).trans
      (pow_le_pow_right₀ hH (show k+4 ≤ k+5 by omega)))
  have hr21 := hEuler N (by omega) _ L21 D Z ((N : ℝ)^η) F
    hgeom.2.2.2.1 (rpow_pos_of_pos hNr _) hF.le hmod
    (fun c hc => (hf21.1 c hc).2) hf21.2
  have hr : L20.R2 D Z + L21.R2 D Z ≤ (ε/2)*boxTheta N Q W := by
    calc
      _ ≤ 2*C*F*N*((1+log N)*log N^4/((N : ℝ)^η*log 2)) := by linarith
      _ ≤ 2*C*F*N*((2*log N)*log N^4/((N : ℝ)^η*log 2)) := by
        gcongr
        linarith
      _ = (4*C*F/log 2)*N*log N^5/(N : ℝ)^η := by ring
      _ ≤ _ := hT1 N hN1 i Δ V hb
  obtain ⟨hs20, hs21⟩ := hsmall Z hpow.2.2.2.1 hpow.2.2.2.2.1
  have hG20 : H^(k+4+1) ≤ G := pow_le_pow_right₀ hH (by omega)
  have hG21 : H^(k+5+1) = G := by congr 1
  have hs20' := hs20.trans (mul_le_mul_of_nonneg_right hG20 (sqrt_nonneg Q))
  have hs21' : smallOutputMassReal N Z W (family21 N W R a3 b) (Fin.last 4) b ≤ G*Z := by
    simpa only [hG21] using hs21
  have hsmallrel :
      smallOutputMassReal N Z W (family20 N W R a2 a3 b) (Fin.last 3) b +
      smallOutputMassReal N Z W (family21 N W R a3 b) (Fin.last 4) b ≤
      (ε/2)*boxTheta N Q W := by
    calc
      _ ≤ 2*G*Z := by linarith
      _ = (2*G)*N*log N^(0 : ℕ)/(N : ℝ)^(1-β) := hpow.2.2.2.2.2 (2*G)
      _ ≤ _ := hT2 N hN2' i Δ V hb
  exact ⟨hr, hsmallrel, by linarith⟩

/-- The actual finite pair, with only its original main term and R1 left unpaid.
No multiplicity factor multiplies either boxed sigma. -/
theorem mother_prime_pair_R2_small_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ (T : ℕ) (hT : 4 ≤ T), ∀ (N : ℕ) (hN : T ≤ N),
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ) (hb : wuSourceBox k δ N i Δ V),
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → Even N →
      let hN2 : 2 ≤ N := (show 2 ≤ 4 by omega).trans (hT.trans hN)
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ)^(1/2-δ)
      let D := ⌊Q⌋₊ + 1
      let Z := sqrt Q
      let R := fun d : ℕ => Q/d
      let a2 := fun _ : ℕ => 1/p.kappa2
      let a3 := fun _ : ℕ => 1/p.kappa3
      let b := fun _ : ℕ => 1/p.s
      let L20 := sourceFamily hN2 hδ hδhi hb
        (fun d => HighUnit.primePrefix20 (R d) (a2 d) (a3 d) (b d)) (Fin.last 3) b
      let L21 := sourceFamily hN2 hδ hδhi hb
        (fun d => HighUnit.primePrefix21 (R d) (a3 d) (b d)) (Fin.last 4) b
      HighUnitPrimeOutput.envelope20 N W R a2 a3 b +
        HighUnitPrimeOutput.envelope21 N W R a3 b ≤
        (HighUnit.boxedSigma20 N δ W a2 a3 b + HighUnit.boxedSigma21 N δ W a3 b) *
          ordinaryRosserMainSum true N 1 D Z + (L20.R1 D Z + L21.R1 D Z) +
          ε * boxTheta N Q W := by
  obtain ⟨T, hT, hpay⟩ := mother_R2_closedSmall_payment k hδ hδhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN i Δ V hb p hp hs heven
  have hN2 : 2 ≤ N := (show 2 ≤ 4 by omega).trans (hT.trans hN)
  have hg := omega3_source_sieve_geometry hN2 hδ hδhi
  have hfinite := mother_prime_pair_upper hN2 hδ hδhi hb p heven
    (⌊(N : ℝ)^(1/2-δ)⌋₊+1) (sqrt ((N : ℝ)^(1/2-δ)))
    hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have hpaid := (hpay N hN i Δ V hb p hp hs).2.2
  dsimp only at hfinite hpaid ⊢
  linarith

end Wu2008DoubleSieve.HighUnitSieve
