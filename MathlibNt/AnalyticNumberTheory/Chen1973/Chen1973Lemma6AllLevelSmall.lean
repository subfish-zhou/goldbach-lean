import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21FiniteFinal
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6PositiveLevelSmall
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedQuadraticPointwiseSiegelWalfisz

noncomputable section
open Real Complex
namespace AnalyticNumberTheory.LargeSieve

/-- All actual levels, with the finite-height repair at zero and the corrected
positive-level argument. The fixed-c raw quadratic L(1) premise is explicit. -/
theorem chen1973Lemma6_all_level_actual_cell_small_of_fixedQuadraticL1
    (ε : ℝ) (hε : 0 < ε) (hεu : ε < 1/10) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x ≥ X₀, ∀ L B lastD level k m : ℕ,
      0 < L → 0 < B →
      (L : ℝ) ≤ Real.log x ^ (100 : ℕ) → Real.log x ^ (100 : ℕ) < L+1 →
      (B : ℝ) ≤ (x : ℝ)^((13:ℝ)/30) → (x : ℝ)^((13:ℝ)/30) < B+1 →
      L * 2^level ≤ 2*lastD → (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε) →
      (∀ d ∈ chen1973Lemma6ConductorBlock x L 0, ∀ χ : PrimitiveCharacter d,
        χ.1^2 = 1 → c*(d:ℝ)^(-(1/10000:ℝ)) ≤
          (chen1973Lemma6PrimitiveLValue d 1 χ).re) →
      chen1973Lemma6NmBlockActual x L level B k m ≤ C*x/Real.log x^20 := by
  obtain ⟨Cp, hCp, Xp, hp⟩ := chen1973Lemma6_positive_level_actual_cell_small ε hε hεu
  obtain ⟨Xz, hz⟩ := chen1973Lemma6_equation21_levelZero_eventually_of_fixedSiegel c hc
  let R := max Xp (max 3 (Real.exp 1))
  refine ⟨max Cp 1, hCp.trans_le (le_max_left _ _), max Xz ⌈R⌉₊, ?_⟩
  intro x hx L B lastD level k m hL hB hLl hLu hBl hBu hLast hcut hSiegel
  have hxz : Xz ≤ x := (le_max_left _ _).trans hx
  have hxc : ⌈R⌉₊ ≤ x := (le_max_right _ _).trans hx
  have hxR : R ≤ (x:ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hxc)
  have hxP : Xp ≤ (x:ℝ) := (le_max_left _ _).trans hxR
  have hx3R : (3:ℝ) ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hxR)
  have hx3 : 3 ≤ x := by exact_mod_cast hx3R
  have hxexp : Real.exp 1 ≤ (x:ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hxR)
  have hlog : (1:ℝ) ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hxexp
  by_cases hzero : level = 0
  · subst level
    have P : Chen1973Lemma6Eq21SourceParameters x L B k m k :=
      ⟨hx3, hL, hB, le_rfl, hlog, hLl, hLu, hBl, hBu⟩
    have h := hz x hxz L B k m k P hSiegel
    apply h.trans
    simpa only [one_mul] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right Cp 1) (Nat.cast_nonneg x))
      (show 0 ≤ Real.log (x:ℝ)^20 by positivity)
  · have h := hp x hxP L B lastD level k m hL hB (by omega)
      hLl hLu hBl hBu hLast hcut
    exact h.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left Cp 1) (Nat.cast_nonneg x)) (by positivity))

/-- Existing raw Landau--Siegel data suffice for the source objects at all levels.
This consumes the input; it does not prove the raw lower bound. -/
theorem chen1973Lemma6_all_level_actual_cell_small_of_rawLandauSiegel
    (hLS : RawLandauSiegelLowerBound) (ε : ℝ) (hε : 0 < ε) (hεu : ε < 1/10) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x ≥ X₀, ∀ L B lastD level k m : ℕ,
      0 < L → 0 < B →
      (L : ℝ) ≤ Real.log x ^ (100 : ℕ) → Real.log x ^ (100 : ℕ) < L+1 →
      (B : ℝ) ≤ (x : ℝ)^((13:ℝ)/30) → (x : ℝ)^((13:ℝ)/30) < B+1 →
      L * 2^level ≤ 2*lastD → (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε) →
      chen1973Lemma6NmBlockActual x L level B k m ≤ C*x/Real.log x^20 := by
  obtain ⟨c, hc, hdata⟩ := hLS (1/10000) (by norm_num)
  obtain ⟨C, hC, X₀, hX⟩ :=
    chen1973Lemma6_all_level_actual_cell_small_of_fixedQuadraticL1 ε hε hεu c hc
  refine ⟨C, hC, X₀, ?_⟩
  intro x hx L B lastD level k m hL hB hLl hLu hBl hBu hLast hcut
  apply hX x hx L B lastD level k m hL hB hLl hLu hBl hBu hLast hcut
  intro d hd χ hquad
  have hd1 := chen1973Lemma6_eq21_one_lt_conductor hd
  let : NeZero d := ⟨Nat.ne_zero_of_lt hd1⟩
  simpa only [chen1973Lemma6PrimitiveLValue, dif_pos hd1] using
    hdata d χ.1 χ.2 hquad (primitiveCharacter_ne_one hd1 χ)

end AnalyticNumberTheory.LargeSieve
