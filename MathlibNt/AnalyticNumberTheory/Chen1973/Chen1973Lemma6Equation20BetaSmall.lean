import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation20SharpBetaAssembly
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6SourceWeightHeight
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Classical Complex Finset MeasureTheory Set Filter
namespace AnalyticNumberTheory.LargeSieve
set_option maxHeartbeats 2400000

lemma eq20small_root_product_fourth (A B C : ℝ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (Real.sqrt A * Real.sqrt (Real.sqrt B) * Real.sqrt (Real.sqrt C)) ^ 4 =
      A^2 * B * C := by
  calc
    _ = ((Real.sqrt A)^2)^2 * (((Real.sqrt (Real.sqrt B))^2)^2) *
        (((Real.sqrt (Real.sqrt C))^2)^2) := by ring
    _ = _ := by
      rw [Real.sq_sqrt hA, Real.sq_sqrt (Real.sqrt_nonneg B),
        Real.sq_sqrt (Real.sqrt_nonneg C), Real.sq_sqrt hB, Real.sq_sqrt hC]

/-- A scalar algebra lemma, preserving conductor and height scales. -/
lemma eq20small_scalar_root_bound
    (A B C c W Q Z t u l : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hc : 0 ≤ c) (hW : 0 ≤ W) (hQ : 0 < Q)
    (hZ : 0 ≤ Z) (ht : 0 ≤ t) (hu : 0 ≤ u) (hl : 0 < l)
    (hAb : A ≤ 2*c*W/Q*Z*t)
    (hBb : B ≤ 186624*c*W*Q/l^4)
    (hCb : C ≤ 60480000000000*W*Q*l^4*u^4) :
    Real.sqrt A * Real.sqrt (Real.sqrt B) * Real.sqrt (Real.sqrt C) ≤
      1000000*(1+c)*W*Real.sqrt Z*Real.sqrt t*u := by
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (4:ℕ) ≠ 0)).mp
  rw [eq20small_root_product_fourth A B C hA hB hC]
  have hp : A^2*B*C ≤ (2*c*W/Q*Z*t)^2 *
      (186624*c*W*Q/l^4) * (60480000000000*W*Q*l^4*u^4) := by
    gcongr
  have heq : (2*c*W/Q*Z*t)^2 * (186624*c*W*Q/l^4) *
      (60480000000000*W*Q*l^4*u^4) =
      45148078080000000000*c^3*W^4*Z^2*t^2*u^4 := by
    field_simp
    ring
  have hc3 : c^3 ≤ (1+c)^4 := by
    calc
      _ ≤ (1+c)^3 := by gcongr; linarith
      _ ≤ (1+c)^4 := pow_le_pow_right₀ (by linarith) (by omega)
  have hnum : 45148078080000000000*c^3 ≤ (1000000:ℝ)^4*(1+c)^4 := by
    calc
      _ ≤ 45148078080000000000*(1+c)^4 := by gcongr
      _ ≤ _ := by gcongr; norm_num
  calc
    _ ≤ 45148078080000000000*c^3*W^4*Z^2*t^2*u^4 := hp.trans_eq heq
    _ ≤ (1000000:ℝ)^4*(1+c)^4*W^4*Z^2*t^2*u^4 := by gcongr
    _ = _ := by
      have hz := Real.sq_sqrt hZ
      have htt := Real.sq_sqrt ht
      calc
        _ = (1000000:ℝ)^4*(1+c)^4*W^4*((Real.sqrt Z)^2)^2*
            ((Real.sqrt t)^2)^2*u^4 := by rw [hz, htt]
        _ = _ := by ring

lemma eq20small_log_nat_nonneg (H : ℕ) : 0 ≤ Real.log (H : ℝ) := by
  exact Real.log_natCast_nonneg H

/-- The three actual moment factors retain `sqrt(Q²+H)`, not a polynomial
replacement of `log Q`. The inverse radius cancels the pair logarithm. -/
theorem eq20small_actual_coefficient_bound
    (x L level B k H D Q : ℕ) (hl : 1 ≤ Real.log (x : ℝ))
    (hB : 0 < B) (hQ : 2 ≤ Q) (hDQ : (Q : ℝ) = 2*(D : ℝ))
    (hYQ : B*2^k ≤ Q) :
    chen1973Lemma6Eq20BetaLinearCoefficient x L level B k H D Q ≤
      1000000*(1+chen1973Lemma6Eq19SharpConstant)*chen1973Lemma6Eq19I x L level *
        Real.sqrt ((Q : ℝ)^2+H) * Real.sqrt (1+Real.log H) *
          (1+Real.log Q) := by
  let c := chen1973Lemma6Eq19SharpConstant
  let W := chen1973Lemma6Eq19I x L level
  let l := Real.log (x : ℝ)
  let r := 1/(2*l)
  let β := chen1973Lemma6Beta x
  let m0 := 1+|β|+r
  have hc : 0 ≤ c := chen1973Lemma6_eq19SharpConstant_pos.le
  have hW : 0 ≤ W := (chen1973Lemma6Eq19I_pos x L level).le
  have hl0 : 0 < l := by dsimp [l]; linarith
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hDr : 0 < (D : ℝ) := by linarith
  have hD_eq : (D : ℝ) = (Q : ℝ)/2 := by linarith only [hDQ]
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg hQ1
  have ht : 0 ≤ 1+Real.log (H : ℝ) := by linarith [eq20small_log_nat_nonneg H]
  have hβ0 : 0 ≤ β := by dsimp [β, chen1973Lemma6Beta]; positivity
  have hβlo : 1/2 ≤ β := by dsimp [β, chen1973Lemma6Beta]; linarith [one_div_pos.mpr hl0]
  have hβhi : β ≤ 3/2 := by
    have hi : 1/l ≤ 1 := (div_le_iff₀ hl0).2 (by dsimp [l]; linarith)
    dsimp [β, chen1973Lemma6Beta]
    dsimp [l] at hi
    linarith
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrhi : r ≤ 1/2 := by
    dsimp [r]
    apply (div_le_iff₀ (by positivity : 0 < 2*l)).2
    dsimp [l]
    linarith
  have hm0 : 0 ≤ m0 := by dsimp [m0]; positivity
  have hm3 : m0 ≤ 3 := by dsimp [m0]; rw [abs_of_nonneg hβ0]; linarith
  have hlogbase : 1 ≤ (Q : ℝ)*(1+m0) := by nlinarith
  have hlog0 : 0 ≤ 1+Real.log ((Q : ℝ)*(1+m0)) := by
    linarith [Real.log_nonneg hlogbase]
  have hlogb : 1+Real.log ((Q : ℝ)*(1+m0)) ≤ 5*(1+Real.log Q) := by
    rw [Real.log_mul hQr.ne' (by positivity : 1+m0 ≠ 0)]
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+m0)
    linarith
  have hY1 : (1:ℝ) ≤ ((B*2^k : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ B*2^k from Nat.mul_pos hB (pow_pos (by omega) k))
  have hYQr : ((B*2^k : ℕ) : ℝ) ≤ Q := by exact_mod_cast hYQ
  have hpow : (((B*2^k : ℕ) : ℝ))^(2-4*β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hY1 (by linarith)
  have hgeom : (Q : ℝ)+(((B*2^k : ℕ) : ℝ))^2/D ≤ 3*Q := by
    rw [hD_eq]
    field_simp
    nlinarith [sq_le_sq₀ (by positivity : (0:ℝ) ≤ ((B*2^k : ℕ) : ℝ))
      (by positivity : (0:ℝ) ≤ Q) |>.2 hYQr]
  have hgeomH : (Q : ℝ)+(H : ℝ)/D ≤ 2/(Q : ℝ)*((Q : ℝ)^2+H) := by
    rw [hD_eq]
    field_simp
    nlinarith [sq_nonneg (Q : ℝ)]
  -- Bound the three moment factors separately before applying the scalar root estimate.
  let A := c*W*((Q : ℝ)+(H : ℝ)/D)*(1+Real.log H)
  let T := 62208*c*W/l^4*((Q : ℝ)+(((B*2^k : ℕ) : ℝ))^2/D)*
    (((B*2^k : ℕ) : ℝ))^(2-4*β)
  let U := chen1973Lemma6Eq20BetaDerivativeCoefficient x L level D Q
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hU : 0 ≤ U := by dsimp [U, chen1973Lemma6Eq20BetaDerivativeCoefficient]; positivity
  have hAb : A ≤ 2*c*W/(Q : ℝ)*((Q : ℝ)^2+H)*(1+Real.log H) := by
    calc
      _ ≤ c*W*(2/(Q : ℝ)*((Q : ℝ)^2+H))*(1+Real.log H) := by
        dsimp [A]
        gcongr
      _ = _ := by ring
  have hTb : T ≤ 186624*c*W*(Q : ℝ)/l^4 := by
    calc
      _ ≤ 62208*c*W/l^4*(3*(Q : ℝ))*1 := by
        dsimp [T]
        gcongr
      _ = _ := by ring
  have hUb : U ≤ 60480000000000*W*(Q : ℝ)*l^4*(1+Real.log Q)^4 := by
    calc
      _ ≤ 16*21000000*W*(Q : ℝ)^2*3^2*(5*(1+Real.log Q))^4 /
          ((D : ℝ)*r^4) := by
        change 16*21000000*W*(Q : ℝ)^2*m0^2*
          (1+Real.log ((Q : ℝ)*(1+m0)))^4/((D : ℝ)*r^4) ≤ _
        gcongr
      _ = _ := by
        rw [hD_eq]
        dsimp [r]
        field_simp
        ring
  exact eq20small_scalar_root_bound A T U c W Q ((Q : ℝ)^2+H)
    (1+Real.log H) (1+Real.log Q) l hA hT hU hc hW hQr (by positivity)
      ht (by linarith) hl0 hAb hTb hUb

lemma eq20small_source_Q_eq_twice_D
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k) :
    (chen1973Lemma6Eq20SourceQ L level : ℝ) =
      2*(chen1973Lemma6Eq20SourceD L level : ℝ) := by
  have hlev : level-1+1 = level := Nat.sub_add_cancel P.hlevel
  unfold chen1973Lemma6Eq20SourceQ chen1973Lemma6Eq20SourceD
  push_cast
  conv_lhs => rw [← hlev, pow_succ]
  ring

/-- Source-cell version: no moment, integral, or scalar budget assumption. -/
theorem eq20small_source_coefficient_bound
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k)
    (H : ℕ) :
    chen1973Lemma6Eq20BetaLinearCoefficient x L level B k H
      (chen1973Lemma6Eq20SourceD L level) (chen1973Lemma6Eq20SourceQ L level) ≤
      1000000*(1+chen1973Lemma6Eq19SharpConstant)*chen1973Lemma6Eq19I x L level *
        Real.sqrt ((chen1973Lemma6Eq20SourceQ L level : ℝ)^2+H) *
          Real.sqrt (1+Real.log H) * (1+Real.log (chen1973Lemma6Eq20SourceQ L level)) :=
  eq20small_actual_coefficient_bound x L level B k H _ _ P.hlog_one P.hB
    (chen1973Lemma6Eq20SourceQ_ge_two P) (eq20small_source_Q_eq_twice_D P) P.hcell.2.1

/-- The actual corrected beta integral with the exact source ceiling and
conductor scales. The caller supplies only the literal complementary cell. -/
theorem eq20small_source_integral_bound
    {x L B lastD level k m : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k)
    (ε : ℝ) :
    let H := chen1973Lemma6Equation20H x level k ε
    let Q := chen1973Lemma6Eq20SourceQ L level
    2*(x : ℝ)^((1:ℝ)/2)*chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m H ≤
      (6000000*Real.pi*(1+chen1973Lemma6Eq19SharpConstant)) *
        (x : ℝ)^((1:ℝ)/2) * Real.log x ^ ((11:ℝ)/10) *
          chen1973Lemma6Eq19I x L level * Real.sqrt ((Q : ℝ)^2+H) *
            Real.sqrt (1+Real.log H) * (1+Real.log Q) := by
  dsimp only
  have hb := chen1973Lemma6_eq20_beta_contribution_budget x L level B k m
    (chen1973Lemma6Equation20H x level k ε) _ _ P.hx P.hB
    (chen1973Lemma6Eq20SourceD_pos P) (chen1973Lemma6Eq20SourceQ_ge_two P)
    (chen1973Lemma6_eq20_conductorBlock_subset_source_Ioc P)
  apply hb.trans
  calc
    _ ≤ 6*Real.pi*(x : ℝ)^((1:ℝ)/2)*Real.log x ^ ((11:ℝ)/10) *
        (1000000*(1+chen1973Lemma6Eq19SharpConstant)*chen1973Lemma6Eq19I x L level *
          Real.sqrt ((chen1973Lemma6Eq20SourceQ L level : ℝ)^2+
            chen1973Lemma6Equation20H x level k ε) *
          Real.sqrt (1+Real.log (chen1973Lemma6Equation20H x level k ε)) *
          (1+Real.log (chen1973Lemma6Eq20SourceQ L level))) :=
      mul_le_mul_of_nonneg_left (eq20small_source_coefficient_bound P _)
        (by positivity)
    _ = _ := by ring

/-- Literal exponential-source conductor scale. -/
def eq20small_Q0 (x level : ℕ) : ℝ :=
  (2:ℝ)^level * Real.log x ^ (100:ℕ)

lemma eq20small_source_Q0_bounds
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k) :
    Real.log x ≤ eq20small_Q0 x level ∧
      eq20small_Q0 x level ≤ 2*(chen1973Lemma6Eq20SourceQ L level : ℝ) := by
  have hp : (1:ℝ) ≤ 2^level := one_le_pow₀ (by norm_num)
  constructor
  · calc
      _ ≤ Real.log x ^ (100:ℕ) := by
        simpa using (pow_le_pow_right₀ P.hlog_one (by norm_num : (1:ℕ) ≤ 100))
      _ ≤ eq20small_Q0 x level :=
        le_mul_of_one_le_left (by positivity) hp
  · have hL : (1:ℝ) ≤ L := by exact_mod_cast P.hL
    have hlog : Real.log x ^ (100:ℕ) ≤ 2*(L : ℝ) := by
      linarith only [P.hL_upper, hL]
    unfold eq20small_Q0 chen1973Lemma6Eq20SourceQ
    push_cast
    calc
      _ ≤ 2^level * (2*(L : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring

lemma eq20small_source_Q_cut
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k)
    (ε : ℝ) (hcut : (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε)) :
    (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1:ℝ)/2-ε) := by
  have hh : (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 2*(lastD : ℝ) := by
    exact_mod_cast P.hcell.2.2
  linarith

lemma eq20small_source_Q0_le_x
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k)
    (ε : ℝ) (hε : 0 ≤ ε) (hx : (16:ℝ) ≤ x)
    (hcut : (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε)) :
    eq20small_Q0 x level ≤ x := by
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (show (1:ℝ) ≤ x by linarith) (show (1:ℝ)/2-ε ≤ 1/2 by linarith)
  rw [← Real.sqrt_eq_rpow] at hpow
  have hQ := eq20small_source_Q_cut P ε hcut
  have hQ0 := (eq20small_source_Q0_bounds P).2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ x by positivity)
  have hs0 := Real.sqrt_nonneg (x : ℝ)
  have hs4 : 4 ≤ Real.sqrt (x : ℝ) := by nlinarith
  nlinarith

/-- Uniform subpower control of the literal exponential weight. Its cutoff is
chosen before `level` and every source-cell parameter. -/
theorem eq20small_Ilx_subpower (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ level : ℕ,
      1 ≤ Real.log (x : ℝ) → Real.log x ≤ eq20small_Q0 x level →
      eq20small_Q0 x level ≤ x →
      chen1973Lemma6Equation20Ilx x level ≤ (x : ℝ)^η := by
  have ht : Tendsto (fun x : ℝ => Real.log (Real.log (Real.log x))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have hev := ht.eventually_ge_atTop (6/η)
  have hev' : ∀ᶠ x : ℝ in atTop, 1 < Real.log x :=
    Real.tendsto_log_atTop.eventually_gt_atTop 1
  obtain ⟨X₀, hX₀⟩ := (eventually_atTop.mp (hev.and hev'))
  refine ⟨max X₀ 2, ?_⟩
  intro x hx level hl hqlo hqhi
  have hxx : X₀ ≤ (x : ℝ) := (le_max_left _ _).trans hx
  obtain ⟨hlarge, hl1⟩ := hX₀ (x : ℝ) hxx
  have hxpos : (0:ℝ) < x := by have := (le_max_right X₀ 2).trans hx; linarith
  have hqpos : 0 < eq20small_Q0 x level := by linarith
  have hq1 : 1 < eq20small_Q0 x level := by linarith
  have hlogqpos : 0 < Real.log (eq20small_Q0 x level) := Real.log_pos hq1
  have hllpos : 0 < Real.log (Real.log (x : ℝ)) := Real.log_pos hl1
  have hll : Real.log (Real.log (x : ℝ)) ≤ Real.log (eq20small_Q0 x level) := by
    gcongr
  have hden : 6/η ≤ Real.log (Real.log (eq20small_Q0 x level)) := by
    apply hlarge.trans
    gcongr
  have hdenpos : 0 < Real.log (Real.log (eq20small_Q0 x level)) :=
    (div_pos (by norm_num) hη).trans_le hden
  have hn : Real.log (eq20small_Q0 x level) ≤ Real.log (x : ℝ) := by gcongr
  have hd : 6 ≤ η*Real.log (Real.log (eq20small_Q0 x level)) := by
    simpa only [mul_comm] using (div_le_iff₀ hη).mp hden
  have hexp : 6*Real.log (eq20small_Q0 x level) /
      Real.log (Real.log (eq20small_Q0 x level)) ≤ Real.log (x : ℝ)*η := by
    apply (div_le_iff₀ hdenpos).2
    nlinarith [mul_le_mul_of_nonneg_right hd (le_of_lt (Real.log_pos (by linarith : (1:ℝ) < x)))]
  unfold chen1973Lemma6Equation20Ilx
  simp only [Real.rpow_natCast]
  change Real.exp (6*Real.log (eq20small_Q0 x level) /
      Real.log (Real.log (eq20small_Q0 x level))) ≤ _
  rw [Real.rpow_def_of_pos hxpos]
  exact Real.exp_le_exp.mpr hexp

lemma eq20small_log_power_absorb (a C : ℝ) (n : ℕ) (ha : 0 < a) (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, C*Real.log x ^ n ≤ x^a := by
  have hh := (isLittleO_log_rpow_rpow_atTop (n : ℝ) ha).bound
    (show 0 < 1/C by positivity)
  filter_upwards [hh, eventually_ge_atTop (1:ℝ)] with x hx hx1
  rw [Real.rpow_natCast] at hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ Real.log x ^ n),
    Real.norm_of_nonneg (by positivity : 0 ≤ x^a)] at hx
  have hdiv : Real.log x ^ n ≤ x^a/C := by simpa [div_eq_mul_inv, mul_comm] using hx
  simpa only [mul_comm] using (le_div_iff₀ hC).mp hdiv

lemma eq20small_H_first_bound
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hcut : (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε)) :
    (2:ℝ)^(2*(level : ℝ)-k)*(x : ℝ)^(-(13:ℝ)/30)*Real.log x ^ (400:ℕ)*
        chen1973Lemma6Equation20Ilx x level ≤
      16*(x : ℝ)^((17:ℝ)/30)*Real.log x ^ (200:ℕ)*chen1973Lemma6Equation20Ilx x level := by
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by have := P.hx; omega)
  have hxpos : (0:ℝ) < x := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hx1
    (show (1:ℝ)/2-ε ≤ 1/2 by linarith)
  rw [← Real.sqrt_eq_rpow] at hpow
  have hQ := eq20small_source_Q_cut P ε hcut
  have hQ0 := (eq20small_source_Q0_bounds P).2
  have hq0 : eq20small_Q0 x level ≤ 4*Real.sqrt x := by linarith
  have hq00 : 0 ≤ eq20small_Q0 x level := by unfold eq20small_Q0; positivity
  have hq02 : eq20small_Q0 x level ^ 2 ≤ 16*(x : ℝ) := by
    have hh := pow_le_pow_left₀ hq00 hq0 2
    nlinarith [Real.sq_sqrt hxpos.le]
  have h2 : (2:ℝ)^(2*(level : ℝ)-k) ≤ ((2:ℝ)^level)^2 := by
    calc
      _ ≤ (2:ℝ)^(2*(level : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) k])
      _ = _ := by rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]; norm_num
  have hI : 0 ≤ chen1973Lemma6Equation20Ilx x level := by
    unfold chen1973Lemma6Equation20Ilx; positivity
  calc
    _ ≤ ((2:ℝ)^level)^2*(x : ℝ)^(-(13:ℝ)/30)*Real.log x ^ (400:ℕ)*
        chen1973Lemma6Equation20Ilx x level := by gcongr
    _ = eq20small_Q0 x level ^ 2*(x : ℝ)^(-(13:ℝ)/30)*Real.log x ^ (200:ℕ)*
        chen1973Lemma6Equation20Ilx x level := by unfold eq20small_Q0; ring
    _ ≤ (16*(x : ℝ))*(x : ℝ)^(-(13:ℝ)/30)*Real.log x ^ (200:ℕ)*
        chen1973Lemma6Equation20Ilx x level := by gcongr
    _ = _ := by
      have he : (x : ℝ)*(x : ℝ)^(-(13:ℝ)/30) = (x : ℝ)^((17:ℝ)/30) := by
        conv_lhs => lhs; rw [← Real.rpow_one (x : ℝ)]
        rw [← Real.rpow_add hxpos]
        norm_num
      calc
        _ = 16*((x : ℝ)*(x : ℝ)^(-(13:ℝ)/30))*Real.log x ^ (200:ℕ)*
          chen1973Lemma6Equation20Ilx x level := by ring
        _ = _ := by rw [he]

/-- Uniform control of the actual rounded source height. In particular,
`level` is not held fixed when selecting the threshold. -/
theorem eq20small_actual_H_subpower :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ L B lastD level k : ℕ,
      ∀ _P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k,
      ∀ ε : ℝ, 0 ≤ ε → (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε) →
      (chen1973Lemma6Equation20H x level k ε : ℝ) ≤ (x : ℝ)^((2:ℝ)/3) := by
  obtain ⟨XI, hXI⟩ := eq20small_Ilx_subpower (1/60) (by norm_num)
  have hl := eq20small_log_power_absorb (1/60) 16 200 (by norm_num) (by norm_num)
  have hp := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/15)).eventually_ge_atTop 2
  obtain ⟨XT, hXT⟩ := eventually_atTop.mp (hl.and hp)
  refine ⟨max 16 (max XI XT), ?_⟩
  intro x hx L B lastD level k P ε hε hcut
  have hx16 : (16:ℝ) ≤ x := (le_max_left _ _).trans hx
  have hxI : XI ≤ (x : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxT : XT ≤ (x : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hI := hXI x hxI level P.hlog_one (eq20small_source_Q0_bounds P).1
    (eq20small_source_Q0_le_x P ε hε hx16 hcut)
  have hI0 : 0 ≤ chen1973Lemma6Equation20Ilx x level := by
    unfold chen1973Lemma6Equation20Ilx; positivity
  obtain ⟨hlog, hgap⟩ := hXT (x : ℝ) hxT
  have hfirst := eq20small_H_first_bound P ε hε hcut
  have hfirst' : (2:ℝ)^(2*(level : ℝ)-k)*(x : ℝ)^(-(13:ℝ)/30)*
      Real.log x ^ (400:ℕ)*chen1973Lemma6Equation20Ilx x level ≤ (x : ℝ)^((3:ℝ)/5) := by
    apply hfirst.trans
    calc
      _ = (x : ℝ)^((17:ℝ)/30)*(16*Real.log x ^ (200:ℕ))*
        chen1973Lemma6Equation20Ilx x level := by ring
      _ ≤ (x : ℝ)^((17:ℝ)/30)*(x : ℝ)^((1:ℝ)/60)*(x : ℝ)^((1:ℝ)/60) := by gcongr
      _ = _ := by rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]; norm_num
  have hsecond : (x : ℝ)^((1:ℝ)/2-ε) ≤ (x : ℝ)^((3:ℝ)/5) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hreal : chen1973Lemma6Equation20HReal x level k ε ≤ (x : ℝ)^((3:ℝ)/5) :=
    max_le hfirst' hsecond
  have hreal0 : 0 ≤ chen1973Lemma6Equation20HReal x level k ε := by
    unfold chen1973Lemma6Equation20HReal
    exact le_trans (by positivity) (le_max_right _ _)
  have hceil : (chen1973Lemma6Equation20H x level k ε : ℝ) <
      chen1973Lemma6Equation20HReal x level k ε+1 := Nat.ceil_lt_add_one hreal0
  have hp1 := Real.one_le_rpow hx1 (by norm_num : (0:ℝ) ≤ 3/5)
  calc
    _ ≤ 2*(x : ℝ)^((3:ℝ)/5) := by linarith
    _ ≤ (x : ℝ)^((1:ℝ)/15)*(x : ℝ)^((3:ℝ)/5) := by gcongr
    _ = _ := by rw [← Real.rpow_add hxpos]; norm_num

/-- Actual finite maximum W, uniformly bounded using the proved W²≤Ilx bridge. -/
theorem eq20small_actual_W_subpower (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ L B lastD level k : ℕ,
      ∀ _P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k,
      ∀ ε : ℝ, 0 ≤ ε → (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε) →
      chen1973Lemma6Eq19I x L level ≤ (x : ℝ)^η := by
  obtain ⟨XI, hXI⟩ := eq20small_Ilx_subpower η hη
  obtain ⟨XW, hXW⟩ := chen1973Lemma6_actual_W_sq_le_Ilx_eventually
  refine ⟨max 16 (max XI XW), ?_⟩
  intro x hx L B lastD level k P ε hε hcut
  have hx16 : (16:ℝ) ≤ x := (le_max_left _ _).trans hx
  have hxI : XI ≤ (x : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxW : XW ≤ (x : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hI := hXI x hxI level P.hlog_one (eq20small_source_Q0_bounds P).1
    (eq20small_source_Q0_le_x P ε hε hx16 hcut)
  have hWsq := hXW x hxW L level P.hL_lower
  have hW1 : 1 ≤ chen1973Lemma6Eq19I x L level := by
    unfold chen1973Lemma6Eq19I
    exact Finset.le_max' _ 1 (by simp)
  have hWI : chen1973Lemma6Eq19I x L level ≤ chen1973Lemma6Equation20Ilx x level := by
    calc
      _ ≤ chen1973Lemma6Eq19I x L level ^ 2 := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ hW1 (by norm_num : (1:ℕ) ≤ 2))
      _ ≤ _ := hWsq
  exact hWI.trans hI

/-- Pointwise scalar payment envelope. The input bounds here are elementary
real inequalities; the source theorem below derives all of them internally. -/
lemma eq20small_scalar_power_envelope (x W C ε : ℝ) (H Q : ℕ)
    (hx : 16 ≤ x) (hl : 1 ≤ Real.log x) (hC : 0 ≤ C)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1/10) (hW0 : 0 ≤ W)
    (hW : W ≤ x^(ε/8)) (hH : (H : ℝ) ≤ x^((2:ℝ)/3))
    (hQ1 : 1 ≤ Q) (hQ : (Q : ℝ) ≤ 2*x^((1:ℝ)/2-ε)) :
    C*x^((1:ℝ)/2)*Real.log x ^ ((11:ℝ)/10)*W*
        Real.sqrt ((Q : ℝ)^2+H)*Real.sqrt (1+Real.log H)*(1+Real.log Q) ≤
      12*C*x^(1-7*ε/8)*Real.log x ^ (4:ℕ) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := by linarith
  let R := x^((1:ℝ)/2-ε)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hH2 : (H : ℝ) ≤ R^2 := by
    apply hH.trans
    dsimp [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num; linarith)
  have hroot : Real.sqrt ((Q : ℝ)^2+H) ≤ 3*R := by
    apply (Real.sqrt_le_left (by positivity)).2
    have hQ2 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Q) hQ 2
    change (Q : ℝ)^2 ≤ (2*R)^2 at hQ2
    nlinarith [sq_nonneg R]
  have hHx : (H : ℝ) ≤ x := by
    calc
      _ ≤ x^((2:ℝ)/3) := hH
      _ ≤ x^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one _
  have hQx : (Q : ℝ) ≤ x := by
    have hp := Real.rpow_le_rpow_of_exponent_le hx1
      (show (1:ℝ)/2-ε ≤ 1/2 by linarith)
    rw [← Real.sqrt_eq_rpow] at hp
    have hs := Real.sq_sqrt hx0.le
    have hs0 := Real.sqrt_nonneg x
    have hs4 : 4 ≤ Real.sqrt x := by nlinarith
    nlinarith
  have hlogH : Real.log (H : ℝ) ≤ Real.log x := by
    by_cases hHz : H = 0
    · simp only [hHz, Nat.cast_zero, Real.log_zero]; exact hl0
    · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hHz)) hHx
  have hlogQ : Real.log (Q : ℝ) ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast (show 0 < Q by omega)) hQx
  have hlogQ0 : 0 ≤ Real.log (Q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hQ1)
  have hlogHroot : Real.sqrt (1+Real.log H) ≤ 2*Real.log x := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith
  have hlogQb : 1+Real.log (Q : ℝ) ≤ 2*Real.log x := by linarith
  have hlogpow : Real.log x ^ ((11:ℝ)/10) ≤ Real.log x ^ (2:ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hl (by norm_num)
  calc
    _ ≤ C*x^((1:ℝ)/2)*Real.log x ^ (2:ℕ)*x^(ε/8)*
        (3*R)*(2*Real.log x)*(2*Real.log x) := by gcongr
    _ = 12*C*(x^((1:ℝ)/2)*x^(ε/8)*x^((1:ℝ)/2-ε))*Real.log x ^ (4:ℕ) := by
      dsimp [R]; ring
    _ = _ := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      rw [show (1:ℝ)/2+ε/8+((1:ℝ)/2-ε) = 1-7*ε/8 by ring]

/-- Complete scalar payment, with its threshold before every moving parameter. -/
theorem eq20small_scalar_budget_paid (ε C : ℝ) (hε : 0 < ε) (hε1 : ε < 1/10)
    (hC : 0 < C) :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → 1 ≤ Real.log x → ∀ W : ℝ, ∀ H Q : ℕ,
      0 ≤ W → W ≤ x^(ε/8) → (H : ℝ) ≤ x^((2:ℝ)/3) → 1 ≤ Q →
      (Q : ℝ) ≤ 2*x^((1:ℝ)/2-ε) →
      C*x^((1:ℝ)/2)*Real.log x ^ ((11:ℝ)/10)*W*
        Real.sqrt ((Q : ℝ)^2+H)*Real.sqrt (1+Real.log H)*(1+Real.log Q) ≤
      x/Real.log x ^ (20:ℕ) := by
  obtain ⟨XT, hXT⟩ := eventually_atTop.mp
    (eq20small_log_power_absorb (7*ε/8) (12*C) 24 (by positivity) (by positivity))
  refine ⟨max 16 XT, ?_⟩
  intro x hx hl W H Q hW0 hW hH hQ1 hQ
  have hx16 : 16 ≤ x := (le_max_left _ _).trans hx
  have hxT : XT ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  apply (eq20small_scalar_power_envelope x W C ε H Q hx16 hl hC.le hε.le hε1
    hW0 hW hH hQ1 hQ).trans
  apply (le_div_iff₀ (pow_pos hl0 20)).2
  calc
    _ = x^(1-7*ε/8)*(12*C*Real.log x ^ (24:ℕ)) := by ring
    _ ≤ x^(1-7*ε/8)*x^(7*ε/8) :=
      mul_le_mul_of_nonneg_left (hXT x hxT) (by positivity)
    _ = x := by rw [← Real.rpow_add hx0]; simp

/-- Full scalar payment of the actual three-moment beta budget, before the
integral theorem is called. All source sizes remain uniformly quantified. -/
theorem eq20small_actual_beta_budget_paid (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/10) :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ L B lastD level k : ℕ,
      ∀ _P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k,
      (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε) →
      6*Real.pi*(x : ℝ)^((1:ℝ)/2)*Real.log x ^ ((11:ℝ)/10)*
        chen1973Lemma6Eq20BetaLinearCoefficient x L level B k
          (chen1973Lemma6Equation20H x level k ε)
          (chen1973Lemma6Eq20SourceD L level) (chen1973Lemma6Eq20SourceQ L level) ≤
        (x : ℝ)/Real.log x ^ (20:ℕ) := by
  let C := 6000000*Real.pi*(1+chen1973Lemma6Eq19SharpConstant)
  have hC : 0 < C := by
    dsimp [C]
    have := chen1973Lemma6_eq19SharpConstant_pos
    positivity
  obtain ⟨XS, hXS⟩ := eq20small_scalar_budget_paid ε C hε hε1 hC
  obtain ⟨XH, hXH⟩ := eq20small_actual_H_subpower
  obtain ⟨XW, hXW⟩ := eq20small_actual_W_subpower (ε/8) (by positivity)
  refine ⟨max XS (max XH XW), ?_⟩
  intro x hx L B lastD level k P hcut
  have hxS : XS ≤ (x : ℝ) := (le_max_left _ _).trans hx
  have hxH : XH ≤ (x : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxW : XW ≤ (x : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hH := hXH x hxH L B lastD level k P ε hε.le hcut
  have hW := hXW x hxW L B lastD level k P ε hε.le hcut
  have hQ := eq20small_source_Q_cut P ε hcut
  have hQ1 : 1 ≤ chen1973Lemma6Eq20SourceQ L level :=
    (by omega : 1 ≤ 2).trans (chen1973Lemma6Eq20SourceQ_ge_two P)
  have hk := mul_le_mul_of_nonneg_left (eq20small_source_coefficient_bound P
      (chen1973Lemma6Equation20H x level k ε))
    (show 0 ≤ 6*Real.pi*(x : ℝ)^((1:ℝ)/2)*Real.log x ^ ((11:ℝ)/10) by positivity)
  apply hk.trans
  have hs := hXS x hxS P.hlog_one _ _ _
    (chen1973Lemma6Eq19I_pos x L level).le hW hH hQ1 hQ
  dsimp only [C] at hs
  convert hs using 1 <;> first | rfl | ring

/-- The actual corrected beta contribution is paid by `x/log^20 x`.
Only the literal source cell and its ordinary geometric cutoff are assumed.
No budget, moment, integrability, growth, or conclusion-shaped predicate is a
premise. The threshold is before all cell parameters, including `level`. -/
theorem eq20small_actual_beta_paid (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/10) :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ L B lastD level k m : ℕ,
      ∀ _P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k,
      (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε) →
      2*(x : ℝ)^((1:ℝ)/2)*chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m
        (chen1973Lemma6Equation20H x level k ε) ≤ (x : ℝ)/Real.log x ^ (20:ℕ) := by
  obtain ⟨X₀, hX₀⟩ := eq20small_actual_beta_budget_paid ε hε hε1
  refine ⟨X₀, ?_⟩
  intro x hx L B lastD level k m P hcut
  exact (chen1973Lemma6_eq20_beta_contribution_budget x L level B k m
    (chen1973Lemma6Equation20H x level k ε) _ _ P.hx P.hB
    (chen1973Lemma6Eq20SourceD_pos P) (chen1973Lemma6Eq20SourceQ_ge_two P)
    (chen1973Lemma6_eq20_conductorBlock_subset_source_Ioc P)).trans
      (hX₀ x hx L B lastD level k P hcut)

/-- Requested existential-constant formulation. The displayed `hQ` is merely
source geometry and is already implied by `P.hcell`; it is not an analytic
payment premise. In fact the stronger theorem above permits the choice `C=1`. -/
theorem chen1973Lemma6_eq20_beta_source_uniform_log20
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/10) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) →
      ∀ L B lastD level k m : ℕ,
      ∀ _P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k,
      (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε) →
      chen1973Lemma6Eq20SourceQ L level ≤ 2*lastD →
      2*(x : ℝ)^((1:ℝ)/2)*chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m
        (chen1973Lemma6Equation20H x level k ε) ≤ C*(x : ℝ)/Real.log x ^ (20:ℕ) := by
  obtain ⟨X₀, hX₀⟩ := eq20small_actual_beta_paid ε hε hε1
  refine ⟨1, by norm_num, X₀, ?_⟩
  intro x hx L B lastD level k m P hcut _hQ
  simpa only [one_mul] using hX₀ x hx L B lastD level k m P hcut

end AnalyticNumberTheory.LargeSieve
