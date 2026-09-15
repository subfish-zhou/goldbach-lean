import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeExceptionBounds

/-! Actual exception payments and canonical prime purification, not raw purification. -/
namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset Real Filter
open scoped Classical

/-- One threshold before N, boxes, mother parameters and the original four words. -/
theorem source_squareRawMass_payment (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      (sourceFamily N δ Δ V p j).squareRawMass ((N : ℝ)^(wuLocalExponent k δ/10)) ≤
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  let H := max 1 (1/η)
  let F := H^(k+3)
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hH : 1 ≤ H := le_max_left _ _
  have hF : 0 < F := pow_pos (lt_of_lt_of_le zero_lt_one hH) _
  obtain ⟨T0,hT04,hT0⟩ := source_squareRawMass_bound k hδ hδhi
  obtain ⟨T1,_,hT1⟩ := omega3_absolute_power_log_relative k 1 hδ hδhi hε
    (show 0 < 4*F by positivity) hη
  obtain ⟨T2,hT2⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget 0 (show (0 : ℝ) < 2 by norm_num) hη)
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T3,hT3⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  let T := max T0 (max T1 (max T2 T3))
  refine ⟨T,hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp j
  have hN0 : T0 ≤ N := (le_max_left _ _).trans hN
  have hN1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : T2 ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN3 : T3 ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  let Y := (N : ℝ)^η
  have hY : 2 ≤ Y := by simpa only [pow_zero, mul_one] using hT2 N hN2
  have hY0 : 0 < Y := by linarith
  have hYm : 0 < Y-1 := by linarith
  have hlog1 := hT3 N hN3
  have h0 := hT0 N hN0 i Δ V hb p hp j Y hY
  have hd : 1/(Y-1) ≤ 2/Y := by
    apply (div_le_div_iff₀ hYm hY0).mpr
    linarith
  change (sourceFamily N δ Δ V p j).squareRawMass Y ≤ _
  calc
    _ ≤ F*N*(1+log N)/(Y-1) := h0
    _ = (F*N*(1+log N))*(1/(Y-1)) := by ring
    _ ≤ (F*N*(1+log N))*(2/Y) := by
      apply mul_le_mul_of_nonneg_left hd
      have : 0 ≤ log (N : ℝ) := by linarith
      positivity
    _ ≤ (F*N*(2*log N))*(2/Y) := by
      gcongr
      linarith
    _ = (4*F)*N*log N^1/(N : ℝ)^η := by dsimp only [Y]; ring
    _ ≤ _ := hT1 N hN1 i Δ V hb

/-- All four raw-square pieces cost a single epsilon, not four epsilons. -/
theorem source_squareRawMass_four_payment (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      (∑ j : Fin 4, (sourceFamily N δ Δ V p j).squareRawMass
        ((N : ℝ)^(wuLocalExponent k δ/10))) ≤
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hm⟩ := source_squareRawMass_payment k hδ hδhi
    (show 0 < ε/4 by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp
  calc
    _ ≤ ∑ _j : Fin 4, ε/4 * boxTheta N ((N : ℝ)^(1/2-δ))
        (convolutionWuWindows N Δ V) := sum_le_sum (fun j _ => hm N hN i Δ V hb p hp j)
    _ = _ := by simp; ring

/-- Only bad prime mass is paid; no dictionary or estimate for bad raw mass is asserted. -/
theorem source_bad_primeMass_payment (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      (sourceFamily N δ Δ V p j).noncoprimePart.primeMass ≤
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let C := (max 1 (1/(wuLocalExponent k δ / 10)))^(k+4) / log 2
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨T1,hT1,hm⟩ := source_bad_primeMass_log_uniform k hδ hδhi
  obtain ⟨T2,_,ha⟩ := omega3_absolute_power_log_relative k 1 hδ hδhi hε hC
    (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T1 T2,hT1.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp j
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hNpos : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by have := hT1.trans hN1; omega)
  apply (hm N hN1 i Δ V hb p hp j).trans
  have hpay := ha N hN2 i Δ V hb
  have hid : C * N * log N ^ 1 / (N : ℝ) ^ (1 : ℝ) =
      (max 1 (1/(wuLocalExponent k δ / 10)))^(k+4) * log N / log 2 := by
    rw [rpow_one, pow_one]
    dsimp [C]
    field_simp
  rw [hid] at hpay
  exact hpay

/-- The original all-four exceptional-prime sum is paid using its explicit 4G log bound. -/
theorem source_bad_primeMass_four_payment (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      (∑ j : Fin 4, (sourceFamily N δ Δ V p j).noncoprimePart.primeMass) ≤
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let C := 4 * (max 1 (1/(wuLocalExponent k δ / 10)))^(k+4) / log 2
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨T1,hT1,hm⟩ := source_bad_primeMass_four_log_uniform k hδ hδhi
  obtain ⟨T2,_,ha⟩ := omega3_absolute_power_log_relative k 1 hδ hδhi hε hC
    (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T1 T2,hT1.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hNpos : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by have := hT1.trans hN1; omega)
  apply (hm N hN1 i Δ V hb p hp).trans
  have hpay := ha N hN2 i Δ V hb
  have hid : C * N * log N ^ 1 / (N : ℝ) ^ (1 : ℝ) =
      4 * (max 1 (1/(wuLocalExponent k δ / 10)))^(k+4) * log N / log 2 := by
    rw [rpow_one, pow_one]
    dsimp [C]
    field_simp
  rw [hid] at hpay
  exact hpay

/-- Each canonical original prime family is purified with one epsilon. -/
theorem source_primeMass_le_rough_payment (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      (sourceFamily N δ Δ V p j).primeMass ≤
        (roughFamily N δ Δ V p j).primeMass +
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT0,h0⟩ := source_primeMass_rough_square_bad k hδ hδhi
  obtain ⟨T1,_,h1⟩ := source_squareRawMass_payment k hδ hδhi
    (show 0 < ε/2 by positivity)
  obtain ⟨T2,_,h2⟩ := source_bad_primeMass_payment k hδ hδhi
    (show 0 < ε/2 by positivity)
  refine ⟨max T0 (max T1 T2),hT0.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp j
  have hN0 := (le_max_left T0 (max T1 T2)).trans hN
  have hN12 := (le_max_right T0 (max T1 T2)).trans hN
  have ha := h0 N hN0 i Δ V hb p hp j
  have hs := h1 N ((le_max_left T1 T2).trans hN12) i Δ V hb p hp j
  have hb' := h2 N ((le_max_right T1 T2).trans hN12) i Δ V hb p hp j
  linarith

/-- Genuine consumption of both all-four exception payments, with one total epsilon. -/
theorem source_primeMass_four_le_rough_payment (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      (∑ j : Fin 4, (sourceFamily N δ Δ V p j).primeMass) ≤
        (∑ j : Fin 4, (roughFamily N δ Δ V p j).primeMass) +
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT0,h0⟩ := source_prime_four_le_rough_square_bad k hδ hδhi
  obtain ⟨T1,_,h1⟩ := source_squareRawMass_four_payment k hδ hδhi
    (show 0 < ε/2 by positivity)
  obtain ⟨T2,_,h2⟩ := source_bad_primeMass_four_payment k hδ hδhi
    (show 0 < ε/2 by positivity)
  refine ⟨max T0 (max T1 T2),hT0.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp
  have hN0 := (le_max_left T0 (max T1 T2)).trans hN
  have hN12 := (le_max_right T0 (max T1 T2)).trans hN
  have ha := h0 N hN0 i Δ V hb p hp
  have hs := h1 N ((le_max_left T1 T2).trans hN12) i Δ V hb p hp
  have hb' := h2 N ((le_max_right T1 T2).trans hN12) i Δ V hb p hp
  linarith

/-- A common threshold for every word and their sum; roughFamily is unchanged. -/
theorem source_prime_purification (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      (∀ j : Fin 4, (sourceFamily N δ Δ V p j).primeMass ≤
        (roughFamily N δ Δ V p j).primeMass +
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) ∧
      (∑ j : Fin 4, (sourceFamily N δ Δ V p j).primeMass) ≤
        (∑ j : Fin 4, (roughFamily N δ Δ V p j).primeMass) +
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T1,hT1,h1⟩ := source_primeMass_le_rough_payment k hδ hδhi hε
  obtain ⟨T2,_,h2⟩ := source_primeMass_four_le_rough_payment k hδ hδhi hε
  refine ⟨max T1 T2,hT1.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp
  exact ⟨h1 N ((le_max_left _ _).trans hN) i Δ V hb p hp,
    h2 N ((le_max_right _ _).trans hN) i Δ V hb p hp⟩

end Wu2008DoubleSieve.FourPrimeNonunit
