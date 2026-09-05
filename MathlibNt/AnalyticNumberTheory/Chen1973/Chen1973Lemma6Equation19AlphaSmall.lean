import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6SourceWeightHeight
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19DyadicAlphaMoment
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19FixedPowerEnvelopes
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation20BetaIntegral
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17CorrectedAssembly

noncomputable section
open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction
namespace AnalyticNumberTheory.LargeSieve
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Real source conductor before the rounding of L. -/
def eq19AlphaQ0 (x level : ℕ) : ℝ := (2 : ℝ)^level * Real.log x ^ (100 : ℕ)

lemma eq19Alpha_source_geometry {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k)
    (hQ : chen1973Lemma6Eq19SourceQ L level ≤ 2 * lastD) :
    chen1973Lemma6Eq19SourceQ L level = 2 * chen1973Lemma6Eq19SourceD L level ∧
    chen1973Lemma6Eq19SourceQ L level ≤ 2 * (B * 2^k) ∧
    (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ eq19AlphaQ0 x level ∧
    eq19AlphaQ0 x level ≤ 2 * chen1973Lemma6Eq19SourceQ L level := by
  have hp : level - 1 + 1 = level := Nat.sub_add_cancel P.hlevel
  have hpow : (2 : ℕ)^level = 2 * 2^(level-1) := by
    calc
      (2 : ℕ)^level = 2^(level-1+1) := congrArg (fun j : ℕ => (2 : ℕ)^j) hp.symm
      _ = 2 * 2^(level-1) := by rw [pow_succ]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold chen1973Lemma6Eq19SourceQ chen1973Lemma6Eq19SourceD
    rw [hpow]; ring
  · rcases chen1973Lemma6Eq19SourceParameters.branch P with hb | hb
    · exact hQ.trans (Nat.mul_le_mul_left 2 (by simpa [chen1973Lemma6Eq19PairD] using hb.le))
    · have hb' : chen1973Lemma6Eq19SourceQ L level ≤ B * 2^k := by
        simpa [chen1973Lemma6Eq19PairD] using hb.2.le
      omega
  · unfold eq19AlphaQ0 chen1973Lemma6Eq19SourceQ
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left P.hL_lower (show 0 ≤ (2 : ℝ)^level by positivity)]
  · have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast P.hL
    have hu : Real.log x ^ (100 : ℕ) ≤ 2 * L := by linarith [P.hL_upper]
    unfold eq19AlphaQ0 chen1973Lemma6Eq19SourceQ
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hu (show 0 ≤ (2 : ℝ)^level by positivity)]

/-- The exponential source I leaves ninety logarithmic powers after division
by Q0.  The log-log condition is uniform in every dyadic level. -/
lemma eq19Alpha_I_log90 {x level : ℕ}
    (hu : 1 ≤ Real.log x) (htt : 60 ≤ Real.log (Real.log (eq19AlphaQ0 x level))) :
    1 ≤ chen1973Lemma6Equation20Ilx x level ∧
    chen1973Lemma6Equation20Ilx x level * Real.log x ^ (90 : ℕ) ≤ eq19AlphaQ0 x level := by
  let u := Real.log (x : ℝ)
  let R := eq19AlphaQ0 x level
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hR : u ^ (100 : ℕ) ≤ R := by
    dsimp [R, eq19AlphaQ0, u]
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hR1 : 1 ≤ R := (one_le_pow₀ hu).trans hR
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hlogu : 100 * Real.log u ≤ Real.log R := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (pow_pos hu0 100) hR
  have ht : 0 < Real.log (Real.log R) := by change 60 ≤ Real.log (Real.log R) at htt; linarith
  have hexp : 6 * Real.log R / Real.log (Real.log R) ≤ Real.log R / 10 := by
    apply (div_le_iff₀ ht).mpr
    have hm := mul_le_mul_of_nonneg_left htt hlR
    nlinarith
  have hIeq : chen1973Lemma6Equation20Ilx x level =
      Real.exp (6 * Real.log R / Real.log (Real.log R)) := by
    simp [chen1973Lemma6Equation20Ilx, R, eq19AlphaQ0, Real.rpow_natCast]
  constructor
  · rw [hIeq]
    exact Real.one_le_exp_iff.mpr (by positivity)
  · rw [hIeq]
    calc
      Real.exp (6 * Real.log R / Real.log (Real.log R)) * u^90 =
          Real.exp (6 * Real.log R / Real.log (Real.log R) + 90 * Real.log u) := by
        rw [Real.exp_add]
        congr 1
        simpa only [Real.log_pow, Nat.cast_ofNat] using (Real.exp_log (pow_pos hu0 90)).symm
      _ ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr (by linarith)
      _ = R := Real.exp_log hR0

lemma eq19Alpha_loglog_eventually :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ level : ℕ,
      1 ≤ Real.log x ∧ 60 ≤ Real.log (Real.log (eq19AlphaQ0 x level)) := by
  refine ⟨Real.exp (Real.exp (Real.exp 60)), ?_⟩
  intro x hx level
  have hx0 : 0 < (x : ℝ) := (Real.exp_pos _).trans_le hx
  have hu : Real.exp (Real.exp 60) ≤ Real.log (x : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos _) hx
  have hu1 : 1 ≤ Real.log (x : ℝ) :=
    (Real.one_le_exp_iff.mpr (Real.exp_pos _).le).trans hu
  have hR : Real.log (x : ℝ) ≤ eq19AlphaQ0 x level := by
    have hp : Real.log (x : ℝ) ≤ Real.log (x : ℝ)^ (100 : ℕ) := by
      simpa using pow_le_pow_right₀ hu1 (show 1 ≤ (100 : ℕ) by omega)
    refine hp.trans ?_
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hlog : Real.exp 60 ≤ Real.log (eq19AlphaQ0 x level) := by
    simpa using Real.log_le_log (Real.exp_pos _) (hu.trans hR)
  exact ⟨hu1, by simpa using Real.log_le_log (Real.exp_pos _) hlog⟩

/-- True-height source payment, already strong enough for dyadic alpha smallness.
No cellwise existential or conclusion-shaped analytic source is used. -/
theorem eq19Alpha_source_weight_budget :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ L B lastD level k : ℕ,
      Chen1973Lemma6Eq19SourceParameters x L B lastD level k →
      chen1973Lemma6Eq19SourceQ L level ≤ 2 * lastD →
      chen1973Lemma6Eq19I x L level ^ 2 * Real.log x ^ (90 : ℕ) ≤
          2 * chen1973Lemma6Eq19SourceQ L level ∧
      (chen1973Lemma6Eq19SourceQ L level : ℝ) * Real.log x ^ (100 : ℕ) *
          chen1973Lemma6Eq19I x L level ^ 2 ≤ chen1973Lemma6Eq19PrintedHeight x level := by
  obtain ⟨X₁, hX₁⟩ := chen1973Lemma6_actual_W_sq_le_Ilx_eventually
  obtain ⟨X₂, hX₂⟩ := chen1973Lemma6_eq19_printedHeight_weight_payment
  obtain ⟨X₃, hX₃⟩ := eq19Alpha_loglog_eventually
  refine ⟨max X₁ (max X₂ X₃), ?_⟩
  intro x hx L B lastD level k P hQ
  have hx₁ := (le_max_left X₁ (max X₂ X₃)).trans hx
  have hx₂ := (le_max_left X₂ X₃).trans ((le_max_right X₁ (max X₂ X₃)).trans hx)
  have hx₃ := (le_max_right X₂ X₃).trans ((le_max_right X₁ (max X₂ X₃)).trans hx)
  have hI := (eq19Alpha_I_log90 P.hlog_one (hX₃ x hx₃ level).2).2
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ chen1973Lemma6Equation20Ilx x level * Real.log x ^ (90 : ℕ) :=
        mul_le_mul_of_nonneg_right (hX₁ x hx₁ L level P.hL_lower) (by positivity)
      _ ≤ eq19AlphaQ0 x level := hI
      _ ≤ _ := (eq19Alpha_source_geometry P hQ).2.2.2
  · exact (hX₂ x hx₂ L level P.hL_lower).1

/-- Height logarithms are controlled only after imposing the honest source
conductor cap.  No fixed-level convention is hidden in this statement. -/
lemma eq19Alpha_printedHeight_logs {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k)
    (hQ : chen1973Lemma6Eq19SourceQ L level ≤ 2 * lastD)
    (hcap : (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ 2 * (x : ℝ)^((1 : ℝ)/2))
    (htt : 60 ≤ Real.log (Real.log (eq19AlphaQ0 x level))) :
    2 ≤ chen1973Lemma6Eq19PrintedHeight x level ∧
    1 + Real.log (chen1973Lemma6Eq19PrintedHeight x level + 1 : ℕ) ≤ 120 * Real.log x ∧
    Real.log (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ 4 * Real.log x := by
  let u := Real.log (x : ℝ)
  let R := eq19AlphaQ0 x level
  let J := chen1973Lemma6Equation20Ilx x level
  let T := chen1973Lemma6Eq19PrintedHeightReal x level
  have hu : 1 ≤ u := P.hlog_one
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by have := P.hx; omega)
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hroot : (x : ℝ)^((1 : ℝ)/2) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 (show (1 : ℝ)/2 ≤ 1 by norm_num)
  have hRbound : R ≤ 4 * x := by
    have h := (eq19Alpha_source_geometry P hQ).2.2.2
    dsimp [R]
    nlinarith
  have hRlow : u^(100 : ℕ) ≤ R :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hR1 : 1 ≤ R := (one_le_pow₀ hu).trans hRlow
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRlog : Real.log R ≤ 4*u := by
    have hh := Real.log_le_log hR0 hRbound
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx0.ne'] at hh
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    dsimp [u] at *
    linarith
  obtain ⟨hJ1, hJR⟩ := eq19Alpha_I_log90 P.hlog_one htt
  change 1 ≤ J at hJ1
  change J * u^90 ≤ R at hJR
  have hJ0 : 0 < J := lt_of_lt_of_le zero_lt_one hJ1
  have hJle : J ≤ R := (le_mul_of_one_le_right hJ0.le (one_le_pow₀ hu)).trans hJR
  have hJlog : Real.log J ≤ 4*u := (Real.log_le_log hJ0 hJle).trans hRlog
  have hTeq : T = R * u^100 * J := by
    dsimp [T, R, u, eq19AlphaQ0, chen1973Lemma6Eq19PrintedHeightReal, J]
    ring
  have hT1 : 1 ≤ T := by
    rw [hTeq]
    calc
      1 = (1 : ℝ) * 1 * 1 := by norm_num
      _ ≤ R * u^100 * J := by gcongr; exact one_le_pow₀ hu
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hTlog : Real.log T ≤ 108*u := by
    rw [hTeq, Real.log_mul (by positivity) hJ0.ne', Real.log_mul hR0.ne' (by positivity),
      Real.log_pow]
    have hlu := Real.log_le_sub_one_of_pos hu0
    norm_num
    linarith
  have hceil : (chen1973Lemma6Eq19PrintedHeight x level : ℝ) < T + 1 :=
    Nat.ceil_lt_add_one hT0.le
  have hplus : ((chen1973Lemma6Eq19PrintedHeight x level + 1 : ℕ) : ℝ) ≤ 3*T := by
    push_cast
    linarith
  have hlogplus : Real.log (chen1973Lemma6Eq19PrintedHeight x level + 1 : ℕ) ≤ 110*u := by
    have hh := Real.log_le_log (by positivity) hplus
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hT0.ne'] at hh
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hH2 : 2 ≤ chen1973Lemma6Eq19PrintedHeight x level := by
    have hp : (2 : ℝ) ≤ (2 : ℝ)^level := by
      simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) P.hlevel
    have hT2 : 2 ≤ T := by
      dsimp [T, chen1973Lemma6Eq19PrintedHeightReal]
      have hpow : 1 ≤ Real.log (x : ℝ)^(200 : ℕ) := one_le_pow₀ P.hlog_one
      have := mul_le_mul_of_nonneg_right hp (show 0 ≤ Real.log (x : ℝ)^(200 : ℕ) by positivity)
      have := mul_le_mul_of_nonneg_left hJ1 (show 0 ≤ (2 : ℝ)^level * Real.log (x : ℝ)^(200 : ℕ) by positivity)
      nlinarith
    have hh : (2 : ℝ) ≤ chen1973Lemma6Eq19PrintedHeight x level := hT2.trans (Nat.le_ceil T)
    exact_mod_cast hh
  refine ⟨hH2, by change 1 + _ ≤ 120*u; linarith, ?_⟩
  have hQpos : (0 : ℝ) < chen1973Lemma6Eq19SourceQ L level := by
    exact_mod_cast chen1973Lemma6Eq19SourceQ_pos P
  exact (Real.log_le_log hQpos (eq19Alpha_source_geometry P hQ).2.2.1).trans hRlog

/-- Algebraic consequences of the source weight ledger. -/
lemma eq19Alpha_ratios {u W D Q H : ℝ}
    (hu : 1 ≤ u) (hW : 1 ≤ W) (hD : 0 < D) (hH : 0 < H)
    (hQD : Q = 2*D) (hWQ : W^2*u^90 ≤ 2*Q) (hWH : Q*u^100*W^2 ≤ H) :
    W^2 * (Q/H + 1/D) ≤ 5/u^90 ∧ W^2*Q^2/H^2 ≤ 1/u^200 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hQ0 : 0 < Q := by rw [hQD]; positivity
  have hW2 : 1 ≤ W^2 := one_le_pow₀ hW
  have hmain : W^2*Q/H ≤ 1/u^100 := by
    apply (div_le_div_iff₀ hH (pow_pos hu0 100)).mpr
    nlinarith [hWH]
  have hDpart : W^2/D ≤ 4/u^90 := by
    apply (div_le_div_iff₀ hD (pow_pos hu0 90)).mpr
    nlinarith [hWQ]
  have hup : u^90 ≤ u^100 := pow_le_pow_right₀ hu (by omega)
  have hmain' : W^2*Q/H ≤ 1/u^90 := hmain.trans (one_div_le_one_div_of_le (pow_pos hu0 90) hup)
  constructor
  · calc
      W^2*(Q/H+1/D) = W^2*Q/H + W^2/D := by ring
      _ ≤ 1/u^90 + 4/u^90 := add_le_add hmain' hDpart
      _ = 5/u^90 := by ring
  · have hnorm : W*Q/H ≤ 1/u^100 := by
      apply le_trans _ hmain
      apply div_le_div_of_nonneg_right _ hH.le
      apply mul_le_mul_of_nonneg_right _ hQ0.le
      nlinarith
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ W*Q/H) hnorm 2
    rw [div_pow, mul_pow, one_div_pow, ← pow_mul] at hh
    norm_num at hh
    simpa only [one_div] using hh

/-- The complete weighted dyadic budget is small, not merely integrable. -/
lemma eq19Alpha_budget_scalar {u W D Q H t n p ell a : ℝ}
    (hu : 1 ≤ u) (hQ : 0 ≤ Q) (hH : 0 < H)
    (ht : 1 ≤ t) (hn : 0 ≤ n) (hnle : n ≤ 2*t)
    (hp : 0 ≤ p) (hple : p ≤ 4*u)
    (hell : 0 ≤ ell) (hellle : ell ≤ 120*u)
    (ha : 0 ≤ a) (hale : a ≤ 1/H)
    (hmain : W^2*(Q/H+1/D) ≤ 5/u^90)
    (hrem : W^2*Q^2/H^2 ≤ 1/u^200) :
    W^2 * (2*chen1973Lemma6Eq14DyadicConstant*(Q/H+1/D)*ell^5 +
      2*Q*(40*n*Real.sqrt Q*p*a*ell)^2) ≤
      (10*chen1973Lemma6Eq14DyadicConstant*120^5 + 2*(40*2*4*120)^2) / u^80 * t^2 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have ht0 : 0 ≤ t := by linarith
  have hC : 0 ≤ chen1973Lemma6Eq14DyadicConstant := chen1973Lemma6Eq14DyadicConstant_pos.le
  have hmain' : W^2*(2*chen1973Lemma6Eq14DyadicConstant*(Q/H+1/D)*ell^5) ≤
      (10*chen1973Lemma6Eq14DyadicConstant*120^5)/u^80*t^2 := by
    calc
      _ = 2*chen1973Lemma6Eq14DyadicConstant*(W^2*(Q/H+1/D))*ell^5 := by ring
      _ ≤ 2*chen1973Lemma6Eq14DyadicConstant*(5/u^90)*(120*u)^5 := by gcongr
      _ = (10*chen1973Lemma6Eq14DyadicConstant*120^5)/u^85 := by field_simp; ring
      _ ≤ (10*chen1973Lemma6Eq14DyadicConstant*120^5)/u^80 := by
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos hu0 80)
        exact pow_le_pow_right₀ hu (by omega)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht)
  have hrem' : W^2*(2*Q*(40*n*Real.sqrt Q*p*a*ell)^2) ≤
      (2*(40*2*4*120)^2)/u^80*t^2 := by
    calc
      _ ≤ W^2*(2*Q*(40*(2*t)*Real.sqrt Q*(4*u)*(1/H)*(120*u))^2) := by gcongr
      _ = 2*(40*2*4*120)^2*t^2*u^4*(W^2*Q^2/H^2) := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hQ]
        field_simp
      _ ≤ 2*(40*2*4*120)^2*t^2*u^4*(1/u^200) := by gcongr
      _ = (2*(40*2*4*120)^2)/u^196*t^2 := by field_simp
      _ ≤ (2*(40*2*4*120)^2)/u^80*t^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg t)
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos hu0 80)
        exact pow_le_pow_right₀ hu (by omega)
  calc
    _ = W^2*(2*chen1973Lemma6Eq14DyadicConstant*(Q/H+1/D)*ell^5) +
        W^2*(2*Q*(40*n*Real.sqrt Q*p*a*ell)^2) := by ring
    _ ≤ (10*chen1973Lemma6Eq14DyadicConstant*120^5)/u^80*t^2 +
        (2*(40*2*4*120)^2)/u^80*t^2 := add_le_add hmain' hrem'
    _ = _ := by ring

def eq19AlphaBudgetConstant : ℝ :=
  10*chen1973Lemma6Eq14DyadicConstant*120^5 + 2*(40*2*4*120)^2

def eq19AlphaNumeratorConstant : ℝ :=
  Real.sqrt (27*chen1973Lemma6Eq19SharpConstant*eq19AlphaBudgetConstant)

lemma eq19Alpha_pair_shape {Q Y D σ : ℝ} (hQ : 0 ≤ Q) (hY : 1 ≤ Y)
    (hD : 1 ≤ D) (hQY : Q ≤ 2*Y) (hσ : 1 ≤ σ) :
    (Q+Y/D)*Y^(1-2*σ) ≤ 3 := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hr : Y^(1-2*σ) ≤ 1/Y := by
    simpa only [Real.rpow_neg_one, one_div] using
      Real.rpow_le_rpow_of_exponent_le hY (show 1-2*σ ≤ (-1 : ℝ) by linarith)
  have hq : Q/Y ≤ 2 := (div_le_iff₀ hY0).mpr hQY
  have hd : 1/D ≤ 1 := (div_le_iff₀ hD0).mpr (by simpa using hD)
  calc
    _ ≤ (Q+Y/D)*(1/Y) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = Q/Y + 1/D := by field_simp
    _ ≤ 3 := by linarith

/-- Uniform linear-v numerator bound using the new dyadic moments and the
true printed height.  The extra geometric cap is explicit. -/
theorem eq19Alpha_actual_numerator_small :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ L B lastD level k m : ℕ,
      Chen1973Lemma6Eq19SourceParameters x L B lastD level k →
      chen1973Lemma6Eq19SourceQ L level ≤ 2*lastD →
      (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1 : ℝ)/2) →
      ∀ v : ℝ, 0 ≤ v →
      chen1973Lemma6A x L level B k m (chen1973Lemma6Eq19PrintedHeight x level)
        (chen1973Lemma6Alpha x + v*I) ≤
      eq19AlphaNumeratorConstant / Real.log x ^ (40 : ℕ) * (1+v) := by
  obtain ⟨X₁, hX₁⟩ := eq19Alpha_source_weight_budget
  obtain ⟨X₂, hX₂⟩ := eq19Alpha_loglog_eventually
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx L B lastD level k m P hQ hcap v hv
  let u := Real.log (x : ℝ)
  let W := chen1973Lemma6Eq19I x L level
  let D := chen1973Lemma6Eq19SourceD L level
  let Q := chen1973Lemma6Eq19SourceQ L level
  let H := chen1973Lemma6Eq19PrintedHeight x level
  let α := chen1973Lemma6Alpha x
  have hu : 1 ≤ u := P.hlog_one
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  obtain ⟨hWQ, hWH⟩ := hX₁ x ((le_max_left _ _).trans hx) L B lastD level k P hQ
  obtain ⟨hH, hlogH, hlogQ⟩ := eq19Alpha_printedHeight_logs P hQ hcap
    (hX₂ x ((le_max_right _ _).trans hx) level).2
  have hD : 0 < D := chen1973Lemma6Eq19SourceD_pos P
  have hDQ : D < Q := chen1973Lemma6Eq19SourceD_lt_Q P
  have hQ2 : 2 ≤ Q := chen1973Lemma6Eq19SourceQ_ge_two P
  have hW1 : 1 ≤ W := by unfold W chen1973Lemma6Eq19I; exact Finset.le_max' _ 1 (by simp)
  have hW0 : 0 ≤ W := by linarith
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hHr : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by dsimp [H]; omega)
  have hQr : (0 : ℝ) ≤ Q := by positivity
  have hgeom := eq19Alpha_source_geometry P hQ
  have hQD : (Q : ℝ) = 2*(D : ℝ) := by exact_mod_cast hgeom.1
  have hrat := eq19Alpha_ratios hu hW1 hDr hHr hQD hWQ hWH
  have hα : 1 ≤ α := by dsimp [α, chen1973Lemma6Alpha]; exact le_add_of_nonneg_right (by positivity)
  have hα2 : α ≤ 2 := by
    have hh : 1/u ≤ 1 := (div_le_iff₀ hu0).mpr (by simpa using hu)
    dsimp [α, chen1973Lemma6Alpha]
    dsimp [u] at hh
    linarith
  have hs : ‖(α : ℂ)+v*I‖ ≤ 2*(1+v) := by
    have hh := norm_add_le (α : ℂ) ((v : ℂ)*I)
    simp only [norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ α),
      norm_mul, norm_I, mul_one, abs_of_nonneg hv] at hh
    linarith
  have hlogQ0 : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega))
  have hlogH0 : 0 ≤ 1 + Real.log (H+1 : ℕ) := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ (H+1 : ℕ) by exact_mod_cast (Nat.le_add_left 1 H))
    linarith
  have hlogHH : 1 + Real.log (H : ℝ) ≤ 1 + Real.log (H+1 : ℕ) := by
    exact _root_.add_le_add (le_refl 1) (Real.log_le_log hHr (by push_cast; linarith))
  have hpow : ((H+1 : ℕ) : ℝ)^(-α) ≤ 1/(H : ℝ) := by
    calc
      _ ≤ ((H+1 : ℕ) : ℝ)^(-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by push_cast; linarith) (by linarith)
      _ = 1/((H+1 : ℕ) : ℝ) := by simp [Real.rpow_neg_one]
      _ ≤ 1/(H : ℝ) := one_div_le_one_div_of_le hHr (by push_cast; linarith)
  have hbudget : W^2 * chen1973Lemma6Eq14DyadicBudget H D Q (α+v*I) ≤
      eq19AlphaBudgetConstant/u^80*(1+v)^2 := by
    have hb := eq19Alpha_budget_scalar hu hQr hHr
      (show 1 ≤ 1+v by linarith) (norm_nonneg _) hs hlogQ0 hlogQ hlogH0 hlogH
      (Real.rpow_nonneg (by positivity) _) hpow hrat.1 hrat.2
    apply le_trans _ hb
    dsimp [chen1973Lemma6Eq14DyadicBudget]
    simp only [ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
    gcongr
  have hp : (Q+((B*2^k : ℕ) : ℝ)/(D : ℝ))*((B*2^k : ℕ) : ℝ)^(1-2*α) ≤ 3 := by
    apply eq19Alpha_pair_shape hQr (by exact_mod_cast Nat.mul_pos P.hB (pow_pos (by omega) k))
      (by exact_mod_cast hD) _ hα
    exact_mod_cast hgeom.2.1
  have hpref : 9*chen1973Lemma6Eq19SharpConstant*W/u^2 *
      (Q+((B*2^k : ℕ) : ℝ)/(D : ℝ))*((B*2^k : ℕ) : ℝ)^(1-2*α) ≤
      27*chen1973Lemma6Eq19SharpConstant*W := by
    have hc := chen1973Lemma6_eq19SharpConstant_pos.le
    calc
      _ = (9*chen1973Lemma6Eq19SharpConstant*W/u^2)*
        ((Q+((B*2^k : ℕ) : ℝ)/(D : ℝ))*((B*2^k : ℕ) : ℝ)^(1-2*α)) := by ring
      _ ≤ (9*chen1973Lemma6Eq19SharpConstant*W/u^2)*3 := by gcongr
      _ = (27*chen1973Lemma6Eq19SharpConstant*W)/u^2 := by ring
      _ ≤ _ := div_le_self (by positivity) (one_le_pow₀ hu)
  have hAbase := chen1973Lemma6_eq19_A_le_dyadic_moments x L level B k m H D Q P.hx P.hB α v
    hα hH hD hDQ (chen1973Lemma6_eq19_conductorBlock_subset_source_Ioc P)
  have hc : 0 ≤ chen1973Lemma6Eq19SharpConstant := chen1973Lemma6_eq19SharpConstant_pos.le
  have hK : 0 ≤ eq19AlphaBudgetConstant := by
    unfold eq19AlphaBudgetConstant
    have := chen1973Lemma6Eq14DyadicConstant_pos.le
    positivity
  calc
    _ ≤ Real.sqrt (27*chen1973Lemma6Eq19SharpConstant*W) *
        Real.sqrt (W*chen1973Lemma6Eq14DyadicBudget H D Q (α+v*I)) :=
      hAbase.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hpref) (Real.sqrt_nonneg _))
    _ = Real.sqrt (27*chen1973Lemma6Eq19SharpConstant*(W^2*chen1973Lemma6Eq14DyadicBudget H D Q (α+v*I))) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1; ring
    _ ≤ Real.sqrt (27*chen1973Lemma6Eq19SharpConstant*(eq19AlphaBudgetConstant/u^80*(1+v)^2)) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ ≤ eq19AlphaNumeratorConstant/u^40*(1+v) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by unfold eq19AlphaNumeratorConstant; positivity, ?_⟩
      unfold eq19AlphaNumeratorConstant
      rw [mul_pow, div_pow, Real.sq_sqrt (by positivity)]
      apply le_of_eq
      field_simp

/-- Continuity of the actual numerator from its finite sums and primitive L-functions. -/
theorem chen1973Lemma6A_line_continuous
    {x L level B k m H D Q : ℕ} (σ : ℝ) (hD : 0 < D)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    Continuous (fun v : ℝ => chen1973Lemma6A x L level B k m H (σ + v * I)) := by
  unfold chen1973Lemma6A
  apply continuous_finsetSum
  intro d hd
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro χ hχ
  have hdmem := hcell hd
  have hd1 : 1 < d := by
    have hDd : D < d := (Finset.mem_Ioc.mp hdmem).1
    omega
  let : NeZero d := ⟨Nat.ne_zero_of_lt hd1⟩
  have hχne : χ.1 ≠ 1 := by
    intro hχeq
    have hprim := χ.2
    rw [DirichletCharacter.IsPrimitive, hχeq,
      DirichletCharacter.conductor_one] at hprim
    omega
  have hline : Continuous (fun v : ℝ => ((σ) : ℂ) + v * I) := by fun_prop
  have hL : Continuous (fun v : ℝ =>
      chen1973Lemma6PrimitiveLValue d ((σ) + v * I) χ) := by
    unfold chen1973Lemma6PrimitiveLValue
    split
    · exact (χ.1.differentiable_LFunction hχne).continuous.comp hline
    · contradiction
  have hS : Continuous (fun v : ℝ =>
      chen1973Lemma6MobiusPartialSum H ((σ) + v * I) χ) := by
    unfold chen1973Lemma6MobiusPartialSum
    apply continuous_finsetSum
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
    apply Continuous.div continuous_const
    · exact hline.const_cpow (Or.inl hn0)
    · intro v
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl hn0)
  apply Continuous.mul
  · apply Continuous.norm
    apply continuous_finsetSum
    intro pp hpp
    obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
    have hpair : (pp.1 : ℂ) * pp.2 ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hp₁.ne') (by exact_mod_cast hp₂.ne')
    by_cases hlog : Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) = 0
    · simpa [hlog] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
    · apply Continuous.div continuous_const
      · exact (hline.const_cpow (Or.inl hpair)).mul continuous_const
      · intro v
        exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hpair))
          (by exact_mod_cast hlog)
  · exact (continuous_const.sub (hL.mul hS)).norm

/-- Uniform smallness of the actual corrected alpha integral at the printed
height. Only source parameters and explicit geometric caps remain. -/
theorem chen1973Lemma6_eq19_alpha_integrable_and_small :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) →
    ∀ L B lastD level k m : ℕ,
      Chen1973Lemma6Eq19SourceParameters x L B lastD level k →
      chen1973Lemma6Eq19SourceQ L level ≤ 2 * lastD →
      (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ 2 * (x : ℝ)^((1 : ℝ)/2) →
      IntegrableOn (fun v : ℝ =>
        chen1973Lemma6A x L level B k m (chen1973Lemma6Eq19PrintedHeight x level)
          (chen1973Lemma6Alpha x + v * I) /
        chen1973Lemma6Eq17CorrectedKernel x (chen1973Lemma6Alpha x + v * I)) (Ioi 0) ∧
      chen1973Lemma6Eq20CorrectedFirstIntegral x L level B k m
        (chen1973Lemma6Eq19PrintedHeight x level) ≤ C / Real.log x ^ (22 : ℕ) := by
  have hC : 0 < eq19AlphaNumeratorConstant := by
    unfold eq19AlphaNumeratorConstant eq19AlphaBudgetConstant
    have hc := chen1973Lemma6_eq19SharpConstant_pos
    have hd := chen1973Lemma6Eq14DyadicConstant_pos
    positivity
  obtain ⟨X₀, hX₀⟩ := eq19Alpha_actual_numerator_small
  refine ⟨3 * Real.pi * eq19AlphaNumeratorConstant, by positivity, X₀, ?_⟩
  intro x hx L B lastD level k m P hQ hcap
  have hα : (1 : ℝ) ≤ chen1973Lemma6Alpha x := by
    unfold chen1973Lemma6Alpha
    have hu : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one P.hlog_one
    exact le_add_of_nonneg_right (by positivity)
  have hK : 0 ≤ eq19AlphaNumeratorConstant / Real.log x ^ (40 : ℕ) := by positivity
  have hbound := eq20_corrected_linear_integrable_and_bound P.hx
    (show (1 : ℝ)/2 ≤ chen1973Lemma6Alpha x by linarith) hK
    (fun v : ℝ => chen1973Lemma6A x L level B k m
      (chen1973Lemma6Eq19PrintedHeight x level) (chen1973Lemma6Alpha x + v * I))
    (chen1973Lemma6A_line_continuous (chen1973Lemma6Alpha x)
      (chen1973Lemma6Eq19SourceD_pos P)
      (chen1973Lemma6_eq19_conductorBlock_subset_source_Ioc P))
    (by intro v hv; unfold chen1973Lemma6A; positivity)
    (by intro v hv; exact hX₀ x hx L B lastD level k m P hQ hcap v hv.le)
  refine ⟨hbound.1, hbound.2.trans ?_⟩
  have hp : chen1973PerronScale (x : ℝ) ≤ Real.log x ^ (18 : ℕ) := by
    unfold chen1973PerronScale
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le P.hlog_one (by norm_num)
  calc
    _ ≤ 3 * Real.pi * Real.log x ^ (18 : ℕ) *
        (eq19AlphaNumeratorConstant / Real.log x ^ (40 : ℕ)) := by gcongr
    _ = (3 * Real.pi * eq19AlphaNumeratorConstant) / Real.log x ^ (22 : ℕ) := by
      have hu := lt_of_lt_of_le zero_lt_one P.hlog_one
      field_simp

/-- The actual alpha contribution, including the outer factor from corrected (17). -/
theorem chen1973Lemma6_eq19_alpha_contribution_small :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) →
    ∀ L B lastD level k m : ℕ,
      Chen1973Lemma6Eq19SourceParameters x L B lastD level k →
      chen1973Lemma6Eq19SourceQ L level ≤ 2 * lastD →
      (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ 2 * (x : ℝ)^((1 : ℝ)/2) →
      12 * (x : ℝ) * Real.log x ^ 2 *
        chen1973Lemma6Eq20CorrectedFirstIntegral x L level B k m
          (chen1973Lemma6Eq19PrintedHeight x level) ≤ C * x / Real.log x ^ (20 : ℕ) := by
  obtain ⟨C, hC, X₀, hX₀⟩ := chen1973Lemma6_eq19_alpha_integrable_and_small
  refine ⟨12 * C, by positivity, X₀, ?_⟩
  intro x hx L B lastD level k m P hQ hcap
  have hi := (hX₀ x hx L B lastD level k m P hQ hcap).2
  calc
    _ ≤ 12 * (x : ℝ) * Real.log x ^ 2 * (C / Real.log x ^ (22 : ℕ)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (12 * C) * x / Real.log x ^ (20 : ℕ) := by
      have hu := lt_of_lt_of_le zero_lt_one P.hlog_one
      field_simp

/-- Physical wiring into the actual cell. Only beta remains on the right;
this is not a claim that equation (19) as a whole has been paid. -/
theorem chen1973Lemma6_equation19_small_alpha_actual_beta :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) →
    ∀ L B lastD level k m : ℕ,
      Chen1973Lemma6Eq19SourceParameters x L B lastD level k →
      chen1973Lemma6Eq19SourceQ L level ≤ 2 * lastD →
      (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ 2 * (x : ℝ)^((1 : ℝ)/2) →
      chen1973Lemma6NmBlockActual x L level B k m ≤
        C * x / Real.log x ^ (20 : ℕ) + 2 * (x : ℝ)^((1 : ℝ)/2) *
          chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m
            (chen1973Lemma6Eq19PrintedHeight x level) := by
  obtain ⟨C, hC, X₀, hX₀⟩ := chen1973Lemma6_eq19_alpha_contribution_small
  refine ⟨C, hC, X₀, ?_⟩
  intro x hx L B lastD level k m P hQ hcap
  have ha := hX₀ x hx L B lastD level k m P hQ hcap
  have h17 := chen1973Lemma6_equation17_corrected_radial_unconditional
    (x := x) (L := L) (level := level) (B := B) (k := k) (m := m)
    (H := chen1973Lemma6Eq19PrintedHeight x level) P.hx P.hlevel
  unfold chen1973Lemma6Eq17CorrectedRadialFirstIntegral
    chen1973Lemma6Eq17CorrectedRadialSecondIntegral
    chen1973Lemma6Eq17CorrectedRadialKernel at h17
  exact h17.trans (add_le_add ha le_rfl)

end AnalyticNumberTheory.LargeSieve
