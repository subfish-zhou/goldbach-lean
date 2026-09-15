import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19AlphaSmall
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation20UnconditionalFinal

noncomputable section
open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction
namespace AnalyticNumberTheory.LargeSieve
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- The natural dyadic pair scale is at least one, so its real denominators are positive. -/
private lemma eq20Alpha_pair_scale_one {B k : ℕ} (hB : 0 < B) :
    (1 : ℝ) ≤ (B * 2^k : ℕ) := by
  exact_mod_cast Nat.mul_pos hB (pow_pos (by decide : 0 < 2) k)

lemma eq20Alpha_source_geometry {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k) :
    chen1973Lemma6Eq20SourceQ L level = 2 * chen1973Lemma6Eq20SourceD L level ∧
    B * 2^k ≤ chen1973Lemma6Eq20SourceQ L level ∧
    (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ eq19AlphaQ0 x level ∧
    eq19AlphaQ0 x level ≤ 2 * chen1973Lemma6Eq20SourceQ L level := by
  have hp : level - 1 + 1 = level := Nat.sub_add_cancel P.hlevel
  have hpow : (2 : ℕ)^level = 2 * 2^(level-1) := by
    calc
      (2 : ℕ)^level = 2^(level-1+1) := congrArg (fun j : ℕ => (2 : ℕ)^j) hp.symm
      _ = 2 * 2^(level-1) := by rw [pow_succ]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold chen1973Lemma6Eq20SourceQ chen1973Lemma6Eq20SourceD
    rw [hpow]; ring
  · have hh := P.hcell
    simp only [chen1973Lemma6Eq20Cell] at hh
    simpa [chen1973Lemma6Eq20SourceQ] using hh.2.1
  · unfold eq19AlphaQ0 chen1973Lemma6Eq20SourceQ
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left P.hL_lower (show 0 ≤ (2 : ℝ)^level by positivity)]
  · have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast P.hL
    have hu : Real.log x ^ (100 : ℕ) ≤ 2 * L := by linarith [P.hL_upper]
    unfold eq19AlphaQ0 chen1973Lemma6Eq20SourceQ
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hu (show 0 ≤ (2 : ℝ)^level by positivity)]

lemma eq20Alpha_Q0_log {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k)
    (hcap : (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1 : ℝ)/2)) :
    Real.log (eq19AlphaQ0 x level) ≤ 4 * Real.log x := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by have := P.hx; omega)
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hroot : (x : ℝ)^((1 : ℝ)/2) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 (show (1 : ℝ)/2 ≤ 1 by norm_num)
  have hRbound : eq19AlphaQ0 x level ≤ 4 * x := by
    have h := (eq20Alpha_source_geometry P).2.2.2
    nlinarith
  have hR0 : 0 < eq19AlphaQ0 x level := by
    unfold eq19AlphaQ0
    have hu := lt_of_lt_of_le zero_lt_one P.hlog_one
    positivity
  have hh := Real.log_le_log hR0 hRbound
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx0.ne'] at hh
  have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  linarith [P.hlog_one]

lemma eq20Alpha_I_log90_pair {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k)
    (hcap : (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1 : ℝ)/2))
    (hu : (5400 : ℝ)^2 ≤ Real.log x)
    (htt : 60 ≤ Real.log (Real.log (eq19AlphaQ0 x level))) :
    chen1973Lemma6Equation20Ilx x level * Real.log x ^ (90 : ℕ) ≤
      2 * (B * 2^k : ℕ) := by
  let u := Real.log (x : ℝ)
  let R := eq19AlphaQ0 x level
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one P.hlog_one
  have hs : 5400 ≤ Real.sqrt u := (Real.le_sqrt (by norm_num) hu0.le).mpr hu
  have hlu : 90 * Real.log u ≤ u/30 := by
    have hh := eq20_log_height P.hlog_one
    change 1 + Real.log u ≤ 2 * Real.sqrt u at hh
    have hs2 := Real.sq_sqrt hu0.le
    nlinarith [sq_nonneg (Real.sqrt u - 5400)]
  have hRlog := eq20Alpha_Q0_log P hcap
  have hlR0 : 0 ≤ Real.log R := by
    apply Real.log_nonneg
    exact (one_le_pow₀ P.hlog_one).trans
      (le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num)))
  have ht : 0 < Real.log (Real.log R) := by change 60 ≤ Real.log (Real.log R) at htt; linarith
  have hexp : 6 * Real.log R / Real.log (Real.log R) ≤ Real.log R / 10 := by
    apply (div_le_iff₀ ht).mpr
    nlinarith [mul_le_mul_of_nonneg_left htt hlR0]
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by have := P.hx; omega)
  have hI : chen1973Lemma6Equation20Ilx x level * u^90 ≤ (x : ℝ)^((13 : ℝ)/30) := by
    calc
      _ = Real.exp (6 * Real.log R / Real.log (Real.log R) + 90 * Real.log u) := by
        rw [Real.exp_add]
        have hpow : u^90 = Real.exp (90 * Real.log u) := by
          simpa only [Real.log_pow, Nat.cast_ofNat] using (Real.exp_log (pow_pos hu0 90)).symm
        rw [hpow]
        simp [chen1973Lemma6Equation20Ilx, R, eq19AlphaQ0, Real.rpow_natCast]
      _ ≤ Real.exp (Real.log x * ((13 : ℝ)/30)) := by
        apply Real.exp_le_exp.mpr
        change Real.log R ≤ 4*u at hRlog
        change _ ≤ u * _
        linarith
      _ = _ := (Real.rpow_def_of_pos hx0 _).symm
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast P.hB
  have hb : (x : ℝ)^((13 : ℝ)/30) ≤ 2*B := by linarith [P.hB_upper]
  have hY : (B : ℝ) ≤ (B * 2^k : ℕ) := by
    push_cast
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
  exact hI.trans (by nlinarith)

lemma eq20Alpha_first_height_identity (x level k B : ℕ) (hx : 0 < x) (hB : 0 < B) :
    (2 : ℝ) ^ (2 * (level : ℝ) - k) * (x : ℝ) ^ (-(13 : ℝ)/30) *
      Real.log x ^ (400 : ℕ) * chen1973Lemma6Equation20Ilx x level =
    (eq19AlphaQ0 x level)^2 * Real.log x ^ (200 : ℕ) *
      chen1973Lemma6Equation20Ilx x level * B /
      ((B * 2^k : ℕ) * (x : ℝ)^((13 : ℝ)/30)) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  rw [show 2 * (level : ℝ) = (level : ℝ) * 2 by ring,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [Real.rpow_natCast, Real.rpow_two]
  rw [show -(13 : ℝ)/30 = -((13 : ℝ)/30) by ring, Real.rpow_neg hx0.le]
  unfold eq19AlphaQ0
  push_cast
  field_simp

lemma eq20Alpha_height_weight {x L B lastD level k : ℕ} {ε : ℝ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k)
    (hu : 2 ≤ Real.log x)
    (hW : chen1973Lemma6Eq19I x L level ^ 2 ≤ chen1973Lemma6Equation20Ilx x level) :
    (chen1973Lemma6Eq20SourceQ L level : ℝ)^2 / (B * 2^k : ℕ) *
      Real.log x ^ (100 : ℕ) * chen1973Lemma6Eq19I x L level ^ 2 ≤
      chen1973Lemma6Equation20H x level k ε := by
  let u := Real.log (x : ℝ)
  let R := eq19AlphaQ0 x level
  let J := chen1973Lemma6Equation20Ilx x level
  let Q := (chen1973Lemma6Eq20SourceQ L level : ℝ)
  let Y := ((B * 2^k : ℕ) : ℝ)
  let r := (x : ℝ)^((13 : ℝ)/30)
  have hx : 0 < x := by have := P.hx; omega
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hr : 0 < r := Real.rpow_pos_of_pos hx0 _
  have hY : 0 < Y := lt_of_lt_of_le zero_lt_one (eq20Alpha_pair_scale_one P.hB)
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast P.hB
  have hBr : r ≤ 2*B := by dsimp [r]; linarith [P.hB_upper]
  have hu100 : 2 ≤ u^100 := by
    exact hu.trans (by simpa using pow_le_pow_right₀ P.hlog_one (show 1 ≤ (100 : ℕ) by omega))
  have hQR : Q ≤ R := (eq20Alpha_source_geometry P).2.2.1
  have hJ0 : 0 ≤ J := by dsimp [J, chen1973Lemma6Equation20Ilx]; positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hR0 : 0 ≤ R := hQ0.trans hQR
  have hq2 : Q^2 ≤ R^2 := pow_le_pow_left₀ hQ0 hQR 2
  have hpay : r * u^100 ≤ B * u^200 := by
    have hb : r ≤ B*u^100 := hBr.trans (by nlinarith [mul_le_mul_of_nonneg_left hu100 (show (0 : ℝ) ≤ B by positivity)])
    have hh := mul_le_mul_of_nonneg_right hb (pow_nonneg hu0.le 100)
    exact hh.trans_eq (by ring)
  apply le_trans _ (chen1973Lemma6Equation20H_first_le x level k ε)
  rw [eq20Alpha_first_height_identity x level k B hx P.hB]
  change Q^2/Y*u^100*_ ≤ R^2*u^200*J*B/(Y*r)
  apply (le_div_iff₀ (mul_pos hY hr)).mpr
  calc
    _ = Q^2 * chen1973Lemma6Eq19I x L level ^ 2 * (r*u^100) := by field_simp
    _ ≤ R^2 * J * (B*u^200) := by gcongr
    _ = _ := by ring

lemma eq20Alpha_height_logs {x L B lastD level k : ℕ} {ε : ℝ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1/10)
    (hcap : (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1 : ℝ)/2))
    (htt : 60 ≤ Real.log (Real.log (eq19AlphaQ0 x level))) :
    2 ≤ chen1973Lemma6Equation20H x level k ε ∧
    1 + Real.log (chen1973Lemma6Equation20H x level k ε + 1 : ℕ) ≤ 120*Real.log x ∧
    Real.log (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 4*Real.log x := by
  let u := Real.log (x : ℝ)
  let R := eq19AlphaQ0 x level
  let J := chen1973Lemma6Equation20Ilx x level
  let T := chen1973Lemma6Equation20HReal x level k ε
  have hu : 1 ≤ u := P.hlog_one
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by have := P.hx; omega)
  have hx0 := zero_lt_one.trans hx1
  have hRlow : u^100 ≤ R :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hR1 : 1 ≤ R := (one_le_pow₀ hu).trans hRlow
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRlog : Real.log R ≤ 4*u := eq20Alpha_Q0_log P hcap
  obtain ⟨hJ1, hJR⟩ := eq19Alpha_I_log90 P.hlog_one htt
  change 1 ≤ J at hJ1
  change J*u^90 ≤ R at hJR
  have hJ0 : 0 ≤ J := by linarith
  have hJle : J ≤ R := (le_mul_of_one_le_right hJ0 (one_le_pow₀ hu)).trans hJR
  have hpow : (2 : ℝ)^(2*(level : ℝ)-k) ≤ ((2 : ℝ)^level)^2 := by
    calc
      _ ≤ (2 : ℝ)^(2*(level : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (sub_le_self _ (Nat.cast_nonneg _))
      _ = _ := by rw [show 2*(level : ℝ) = (level : ℝ)*2 by ring, Real.rpow_mul (by norm_num)]; simp
  have hxneg : (x : ℝ)^(-(13 : ℝ)/30) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
  have htwo : (1 : ℝ) ≤ (2 : ℝ)^level := one_le_pow₀ (by norm_num)
  have hfirst : (2 : ℝ) ^ (2 * (level : ℝ) - k) *
      (x : ℝ)^(-(13 : ℝ)/30) * u^400 * J ≤ R^5 := by
    calc
      _ ≤ ((2 : ℝ)^level)^2 * 1 * u^400 * R := by gcongr
      _ ≤ ((2 : ℝ)^level)^4 * u^400 * R := by
        gcongr
        simpa using pow_le_pow_right₀ htwo (show 2 ≤ (4 : ℕ) by omega)
      _ = R^5 := by dsimp [R, eq19AlphaQ0, u]; ring
  have hsecond : (x : ℝ)^((1 : ℝ)/2-ε) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1.le (show (1 : ℝ)/2-ε ≤ 1 by linarith)
  have hsecond1 : 1 < (x : ℝ)^((1 : ℝ)/2-ε) :=
    Real.one_lt_rpow hx1 (by linarith)
  have hT1 : 1 < T := hsecond1.trans_le (le_max_right _ _)
  have hT0 : 0 < T := zero_lt_one.trans hT1
  have hTup : T ≤ R^5 * x := by
    apply max_le
    · exact hfirst.trans (le_mul_of_one_le_right (by positivity) hx1.le)
    · exact hsecond.trans (le_mul_of_one_le_left hx0.le (one_le_pow₀ hR1))
  have hTlog : Real.log T ≤ 21*u := by
    have hh := Real.log_le_log hT0 hTup
    rw [Real.log_mul (by positivity) hx0.ne', Real.log_pow] at hh
    norm_num at hh
    dsimp [u] at *
    linarith
  have hceil : (chen1973Lemma6Equation20H x level k ε : ℝ) < T+1 := Nat.ceil_lt_add_one hT0.le
  have hplus : ((chen1973Lemma6Equation20H x level k ε + 1 : ℕ) : ℝ) ≤ 3*T := by
    push_cast
    linarith
  have hlogplus : Real.log (chen1973Lemma6Equation20H x level k ε + 1 : ℕ) ≤ 23*u := by
    have hh := Real.log_le_log (by positivity) hplus
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hT0.ne'] at hh
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  refine ⟨?_, by linarith, ?_⟩
  · have hh : (1 : ℝ) < chen1973Lemma6Equation20H x level k ε := hT1.trans_le (Nat.le_ceil T)
    exact_mod_cast hh
  · have hQpos : (0 : ℝ) < chen1973Lemma6Eq20SourceQ L level := by
      exact_mod_cast (show 0 < chen1973Lemma6Eq20SourceQ L level by have := chen1973Lemma6Eq20SourceQ_ge_two P; omega)
    exact (Real.log_le_log hQpos (eq20Alpha_source_geometry P).2.2.1).trans hRlog

def eq20AlphaEffectiveWeight (x L level B k : ℕ) : ℝ :=
  chen1973Lemma6Eq19I x L level *
    Real.sqrt ((chen1973Lemma6Eq20SourceQ L level : ℝ) / (B*2^k : ℕ))

lemma eq20Alpha_effective_square (x L level B k : ℕ) :
    eq20AlphaEffectiveWeight x L level B k ^ 2 =
      chen1973Lemma6Eq19I x L level ^ 2 *
        ((chen1973Lemma6Eq20SourceQ L level : ℝ) / (B*2^k : ℕ)) := by
  unfold eq20AlphaEffectiveWeight
  rw [mul_pow, Real.sq_sqrt (by positivity)]

lemma eq20Alpha_effective_one {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k) :
    1 ≤ eq20AlphaEffectiveWeight x L level B k := by
  have hW1 : 1 ≤ chen1973Lemma6Eq19I x L level := by
    unfold chen1973Lemma6Eq19I
    exact Finset.le_max' _ 1 (by simp)
  have hY : (0 : ℝ) < (B*2^k : ℕ) :=
    lt_of_lt_of_le zero_lt_one (eq20Alpha_pair_scale_one P.hB)
  have hratio : 1 ≤ (chen1973Lemma6Eq20SourceQ L level : ℝ) / (B*2^k : ℕ) := by
    apply (le_div_iff₀ hY).mpr
    simpa using (show ((B*2^k : ℕ) : ℝ) ≤ chen1973Lemma6Eq20SourceQ L level by
      exact_mod_cast (eq20Alpha_source_geometry P).2.1)
  have hs : 1 ≤ Real.sqrt ((chen1973Lemma6Eq20SourceQ L level : ℝ) / (B*2^k : ℕ)) := by
    simpa using Real.sqrt_le_sqrt hratio
  exact one_le_mul_of_one_le_of_one_le hW1 hs

/-- Uniform effective-weight ledger for the literal complementary maximum/ceiling. -/
theorem eq20Alpha_source_weight_budget :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ L B lastD level k : ℕ,
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1/10 →
    Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k →
    (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1 : ℝ)/2) →
      eq20AlphaEffectiveWeight x L level B k ^ 2 * Real.log x ^ (90 : ℕ) ≤
        2 * chen1973Lemma6Eq20SourceQ L level ∧
      (chen1973Lemma6Eq20SourceQ L level : ℝ) * Real.log x ^ (100 : ℕ) *
        eq20AlphaEffectiveWeight x L level B k ^ 2 ≤ chen1973Lemma6Equation20H x level k ε ∧
      2 ≤ chen1973Lemma6Equation20H x level k ε ∧
      1 + Real.log (chen1973Lemma6Equation20H x level k ε + 1 : ℕ) ≤ 120*Real.log x ∧
      Real.log (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 4*Real.log x := by
  obtain ⟨X₁, hX₁⟩ := chen1973Lemma6_actual_W_sq_le_Ilx_eventually
  obtain ⟨X₂, hX₂⟩ := eq19Alpha_loglog_eventually
  refine ⟨max X₁ (max X₂ (Real.exp ((5400 : ℝ)^2))), ?_⟩
  intro x hx L B lastD level k ε hε0 hε1 P hcap
  have hx₁ := (le_max_left X₁ _).trans hx
  have hx₂ := (le_max_left X₂ _).trans ((le_max_right X₁ _).trans hx)
  have hx₃ := (le_max_right X₂ _).trans ((le_max_right X₁ _).trans hx)
  have hu : (5400 : ℝ)^2 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hx₃
  have hW := hX₁ x hx₁ L level P.hL_lower
  have htt := (hX₂ x hx₂ level).2
  have hWY : chen1973Lemma6Eq19I x L level ^ 2 * Real.log x ^ (90 : ℕ) ≤
      2*(B*2^k : ℕ) :=
    (mul_le_mul_of_nonneg_right hW (by positivity)).trans (eq20Alpha_I_log90_pair P hcap hu htt)
  have hY : (0 : ℝ) < (B*2^k : ℕ) :=
    lt_of_lt_of_le zero_lt_one (eq20Alpha_pair_scale_one P.hB)
  refine ⟨?_, ?_, eq20Alpha_height_logs P hε0 hε1 hcap htt⟩
  · rw [eq20Alpha_effective_square]
    have hh := mul_le_mul_of_nonneg_right hWY
      (show 0 ≤ (chen1973Lemma6Eq20SourceQ L level : ℝ)/(B*2^k : ℕ) by positivity)
    calc
      _ = (chen1973Lemma6Eq19I x L level ^ 2 * Real.log x ^ (90 : ℕ)) *
          ((chen1973Lemma6Eq20SourceQ L level : ℝ)/(B*2^k : ℕ)) := by ring
      _ ≤ _ := hh
      _ = _ := by field_simp
  · rw [eq20Alpha_effective_square]
    convert eq20Alpha_height_weight (ε := ε) P (by linarith) hW using 1
    ring

lemma eq20Alpha_pair_shape {Q Y D σ : ℝ} (hQY : Y ≤ Q) (hY : 1 ≤ Y)
    (hD : 1 ≤ D) (hσ : 1 ≤ σ) :
    (Q+Y/D)*Y^(1-2*σ) ≤ 3*(Q/Y) := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hQ0 : 0 ≤ Q := hY0.le.trans hQY
  have hr : Y^(1-2*σ) ≤ 1/Y := by
    simpa only [Real.rpow_neg_one, one_div] using
      Real.rpow_le_rpow_of_exponent_le hY (show 1-2*σ ≤ (-1 : ℝ) by linarith)
  have hq : 1 ≤ Q/Y := (le_div_iff₀ hY0).mpr (by simpa using hQY)
  have hd : 1/D ≤ 1 := (div_le_iff₀ hD0).mpr (by simpa using hD)
  calc
    _ ≤ (Q+Y/D)*(1/Y) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = Q/Y+1/D := by field_simp
    _ ≤ _ := by linarith

/-- Actual complementary alpha numerator, at the true equation-(20) height. -/
theorem eq20Alpha_actual_numerator_small :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ L B lastD level k m : ℕ,
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1/10 →
    Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k →
    (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1 : ℝ)/2) →
    ∀ v : ℝ, 0 ≤ v →
      chen1973Lemma6A x L level B k m (chen1973Lemma6Equation20H x level k ε)
        (chen1973Lemma6Alpha x + v*I) ≤
      eq19AlphaNumeratorConstant / Real.log x ^ (40 : ℕ) * (1+v) := by
  obtain ⟨X₀, hX₀⟩ := eq20Alpha_source_weight_budget
  refine ⟨X₀, ?_⟩
  intro x hx L B lastD level k m ε hε0 hε1 P hcap v hv
  let u := Real.log (x : ℝ)
  let W := chen1973Lemma6Eq19I x L level
  let E := eq20AlphaEffectiveWeight x L level B k
  let D := chen1973Lemma6Eq20SourceD L level
  let Q := chen1973Lemma6Eq20SourceQ L level
  let Y := ((B*2^k : ℕ) : ℝ)
  let H := chen1973Lemma6Equation20H x level k ε
  let α := chen1973Lemma6Alpha x
  have hu : 1 ≤ u := P.hlog_one
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  obtain ⟨hWQ, hWH, hH, hlogH, hlogQ⟩ := hX₀ x hx L B lastD level k ε hε0 hε1 P hcap
  have hD : 0 < D := chen1973Lemma6Eq20SourceD_pos P
  have hDQ : D < Q := chen1973Lemma6Eq20SourceD_lt_Q P
  have hQ2 : 2 ≤ Q := chen1973Lemma6Eq20SourceQ_ge_two P
  have hW1 : 1 ≤ W := by unfold W chen1973Lemma6Eq19I; exact Finset.le_max' _ 1 (by simp)
  have hW0 : 0 ≤ W := by linarith
  have hE1 : 1 ≤ E := eq20Alpha_effective_one P
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hHr : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by dsimp [H]; omega)
  have hQr : (0 : ℝ) ≤ Q := by positivity
  have hgeom := eq20Alpha_source_geometry P
  have hQD : (Q : ℝ) = 2*(D : ℝ) := by exact_mod_cast hgeom.1
  have hrat := eq19Alpha_ratios hu hE1 hDr hHr hQD hWQ hWH
  have hY : 1 ≤ Y := eq20Alpha_pair_scale_one P.hB
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hQY : Y ≤ Q := by
    dsimp [Y, Q]
    exact_mod_cast hgeom.2.1
  have hEeq : E^2 = W^2*((Q : ℝ)/Y) := eq20Alpha_effective_square x L level B k
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
  have hbudget : E^2 * chen1973Lemma6Eq14DyadicBudget H D Q (α+v*I) ≤
      eq19AlphaBudgetConstant/u^80*(1+v)^2 := by
    have hb := eq19Alpha_budget_scalar hu hQr hHr
      (show 1 ≤ 1+v by linarith) (norm_nonneg _) hs hlogQ0 hlogQ hlogH0 hlogH
      (Real.rpow_nonneg (by positivity) _) hpow hrat.1 hrat.2
    apply le_trans _ hb
    dsimp [chen1973Lemma6Eq14DyadicBudget]
    simp only [ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
    gcongr
  have hp : ((Q : ℝ)+Y/(D : ℝ))*Y^(1-2*α) ≤ 3*((Q : ℝ)/Y) :=
    eq20Alpha_pair_shape hQY hY (by exact_mod_cast hD) hα
  have hc : 0 ≤ chen1973Lemma6Eq19SharpConstant := chen1973Lemma6_eq19SharpConstant_pos.le
  have hpref : 9*chen1973Lemma6Eq19SharpConstant*W/u^2 *
      ((Q : ℝ)+Y/(D : ℝ))*Y^(1-2*α) ≤
      27*chen1973Lemma6Eq19SharpConstant*W*((Q : ℝ)/Y) := by
    calc
      _ = (9*chen1973Lemma6Eq19SharpConstant*W/u^2)*
        (((Q : ℝ)+Y/(D : ℝ))*Y^(1-2*α)) := by ring
      _ ≤ (9*chen1973Lemma6Eq19SharpConstant*W/u^2)*(3*((Q : ℝ)/Y)) := by gcongr
      _ = (27*chen1973Lemma6Eq19SharpConstant*W*((Q : ℝ)/Y))/u^2 := by ring
      _ ≤ _ := div_le_self (by positivity) (one_le_pow₀ hu)
  have hAbase := chen1973Lemma6_eq19_A_le_dyadic_moments x L level B k m H D Q P.hx P.hB α v
    hα hH hD hDQ (chen1973Lemma6_eq20_conductorBlock_subset_source_Ioc P)
  have hK : 0 ≤ eq19AlphaBudgetConstant := by
    unfold eq19AlphaBudgetConstant
    have := chen1973Lemma6Eq14DyadicConstant_pos.le
    positivity
  calc
    _ ≤ Real.sqrt (27*chen1973Lemma6Eq19SharpConstant*W*((Q : ℝ)/Y)) *
        Real.sqrt (W*chen1973Lemma6Eq14DyadicBudget H D Q (α+v*I)) :=
      hAbase.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hpref) (Real.sqrt_nonneg _))
    _ = Real.sqrt (27*chen1973Lemma6Eq19SharpConstant*(E^2*chen1973Lemma6Eq14DyadicBudget H D Q (α+v*I))) := by
      rw [← Real.sqrt_mul (by positivity), hEeq]
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

/-- The actual corrected alpha integral at the original equation-(20) height is
uniformly small. The cutoff and constant precede all cell parameters and epsilon. -/
theorem chen1973Lemma6_eq20_alpha_integrable_and_small :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) →
    ∀ L B lastD level k m : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1/10 →
    Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k →
    (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1 : ℝ)/2) →
      IntegrableOn (fun v : ℝ =>
        chen1973Lemma6A x L level B k m (chen1973Lemma6Equation20H x level k ε)
          (chen1973Lemma6Alpha x + v*I) /
        chen1973Lemma6Eq17CorrectedKernel x (chen1973Lemma6Alpha x + v*I)) (Ioi 0) ∧
      chen1973Lemma6Eq20CorrectedFirstIntegral x L level B k m
        (chen1973Lemma6Equation20H x level k ε) ≤ C / Real.log x ^ (22 : ℕ) := by
  have hC : 0 < eq19AlphaNumeratorConstant := by
    unfold eq19AlphaNumeratorConstant eq19AlphaBudgetConstant
    have hc := chen1973Lemma6_eq19SharpConstant_pos
    have hd := chen1973Lemma6Eq14DyadicConstant_pos
    positivity
  obtain ⟨X₀, hX₀⟩ := eq20Alpha_actual_numerator_small
  refine ⟨3*Real.pi*eq19AlphaNumeratorConstant, by positivity, X₀, ?_⟩
  intro x hx L B lastD level k m ε hε0 hε1 P hcap
  have hα : (1 : ℝ) ≤ chen1973Lemma6Alpha x := by
    unfold chen1973Lemma6Alpha
    have hu := lt_of_lt_of_le zero_lt_one P.hlog_one
    exact le_add_of_nonneg_right (by positivity)
  have hK : 0 ≤ eq19AlphaNumeratorConstant / Real.log x ^ (40 : ℕ) := by positivity
  have hbound := eq20_corrected_linear_integrable_and_bound P.hx
    (show (1 : ℝ)/2 ≤ chen1973Lemma6Alpha x by linarith) hK
    (fun v : ℝ => chen1973Lemma6A x L level B k m
      (chen1973Lemma6Equation20H x level k ε) (chen1973Lemma6Alpha x + v*I))
    (chen1973Lemma6A_line_continuous (chen1973Lemma6Alpha x)
      (chen1973Lemma6Eq20SourceD_pos P)
      (chen1973Lemma6_eq20_conductorBlock_subset_source_Ioc P))
    (by intro v hv; unfold chen1973Lemma6A; positivity)
    (by intro v hv; exact hX₀ x hx L B lastD level k m ε hε0 hε1 P hcap v hv.le)
  refine ⟨hbound.1, hbound.2.trans ?_⟩
  have hp : chen1973PerronScale (x : ℝ) ≤ Real.log x ^ (18 : ℕ) := by
    unfold chen1973PerronScale
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le P.hlog_one (by norm_num)
  calc
    _ ≤ 3*Real.pi*Real.log x ^ (18 : ℕ)*
        (eq19AlphaNumeratorConstant / Real.log x ^ (40 : ℕ)) := by gcongr
    _ = (3*Real.pi*eq19AlphaNumeratorConstant) / Real.log x ^ (22 : ℕ) := by
      have hu := lt_of_lt_of_le zero_lt_one P.hlog_one
      field_simp

/-- Including the literal outside factor `12*x*log(x)^2`. -/
theorem chen1973Lemma6_eq20_alpha_contribution_small :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) →
    ∀ L B lastD level k m : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1/10 →
    Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k →
    (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1 : ℝ)/2) →
      12*(x : ℝ)*Real.log x ^ 2 *
        chen1973Lemma6Eq20CorrectedFirstIntegral x L level B k m
          (chen1973Lemma6Equation20H x level k ε) ≤ C*x/Real.log x ^ (20 : ℕ) := by
  obtain ⟨C, hC, X₀, hX₀⟩ := chen1973Lemma6_eq20_alpha_integrable_and_small
  refine ⟨12*C, by positivity, X₀, ?_⟩
  intro x hx L B lastD level k m ε hε0 hε1 P hcap
  have hi := (hX₀ x hx L B lastD level k m ε hε0 hε1 P hcap).2
  calc
    _ ≤ 12*(x : ℝ)*Real.log x ^ 2 * (C/Real.log x ^ (22 : ℕ)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (12*C)*x/Real.log x ^ (20 : ℕ) := by
      have hu := lt_of_lt_of_le zero_lt_one P.hlog_one
      field_simp

/-- Actual corrected contour wiring: only the genuine beta integral is unpaid. -/
theorem chen1973Lemma6_equation20_small_alpha_actual_beta :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) →
    ∀ L B lastD level k m : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1/10 →
    Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k →
    (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1 : ℝ)/2) →
      chen1973Lemma6NmBlockActual x L level B k m ≤
        C*x/Real.log x ^ (20 : ℕ) + 2*(x : ℝ)^((1 : ℝ)/2) *
          chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m
            (chen1973Lemma6Equation20H x level k ε) := by
  obtain ⟨C, hC, X₀, hX₀⟩ := chen1973Lemma6_eq20_alpha_contribution_small
  refine ⟨C, hC, X₀, ?_⟩
  intro x hx L B lastD level k m ε hε0 hε1 P hcap
  have ha := hX₀ x hx L B lastD level k m ε hε0 hε1 P hcap
  have h17 := chen1973Lemma6_equation17_corrected_radial_unconditional
    (x := x) (L := L) (level := level) (B := B) (k := k) (m := m)
    (H := chen1973Lemma6Equation20H x level k ε) P.hx P.hlevel
  unfold chen1973Lemma6Eq17CorrectedRadialFirstIntegral
    chen1973Lemma6Eq17CorrectedRadialSecondIntegral
    chen1973Lemma6Eq17CorrectedRadialKernel at h17
  exact h17.trans (add_le_add ha le_rfl)

end AnalyticNumberTheory.LargeSieve
