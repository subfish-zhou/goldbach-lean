import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19AlphaSmall
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation20BetaIntegral

noncomputable section
set_option maxHeartbeats 2400000
open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction
namespace AnalyticNumberTheory.LargeSieve

/-- Original Eq19 allocation: pair second, natural Mobius fourth, derivative fourth. -/
def eq19BetaLinearCoefficient (x L level B k H D Q : ℕ) : ℝ :=
  Real.sqrt (9 * chen1973Lemma6Eq19SharpConstant * chen1973Lemma6Eq19I x L level /
    Real.log x ^ 2 * ((Q : ℝ) + ((B*2^k : ℕ) : ℝ)/D) *
    ((B*2^k : ℕ) : ℝ)^(1-2*chen1973Lemma6Beta x)) *
  Real.sqrt (Real.sqrt (chen1973Lemma6Eq19I x L level *
    (chen1973Lemma6Eq19SharpConstant * ((Q : ℝ) + ((H*H : ℕ) : ℝ)/D) *
    (1+Real.log (H*H : ℕ))^4))) *
  Real.sqrt (Real.sqrt (chen1973Lemma6Eq20BetaDerivativeCoefficient x L level D Q))

theorem eq19Beta_actual_linear
    (x L level B k m H D Q : ℕ) (hx : 3 ≤ x) (hB : 0 < B)
    (hD : 0 < D) (hQ : 2 ≤ Q)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) (v : ℝ) :
    chen1973Lemma6B x L level B k m H (chen1973Lemma6Beta x+v*I) ≤
      eq19BetaLinearCoefficient x L level B k H D Q * (1+|v|) := by
  have hl : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hβ : 1/2 ≤ chen1973Lemma6Beta x := by
    unfold chen1973Lemma6Beta
    exact le_add_of_nonneg_right (by positivity)
  have hp := chen1973Lemma6_eq19_dyadic_pair_second_moment_scalar
    x L level B k m D Q hx hB (chen1973Lemma6Beta x) v hβ hD hcell
  have hm := chen1973Lemma6_eq19_mobius_fourth_moment_uniform
    x L level H D Q (chen1973Lemma6Beta x) |v| hD hcell
    (fun t ht => ⟨rfl, hβ⟩) v ⟨neg_abs_le v, le_abs_self v⟩
  have hd := chen1973Lemma6_eq19_LDeriv_fourth_beta x L level D Q hx hD hQ hcell v
  have hheight := eq20_derivative_height_algebra (Q : ℝ) |chen1973Lemma6Beta x|
    (1/(2*Real.log (x : ℝ))) (chen1973Lemma6Eq19I x L level) D v
    (by exact_mod_cast (show 1 ≤ Q by omega)) (abs_nonneg _) (by positivity)
    (chen1973Lemma6Eq19I_pos x L level).le (by positivity)
  have hd' : chen1973Lemma6Eq19LDerivFourthMoment x L level
      (chen1973Lemma6Beta x+v*I) ≤
      chen1973Lemma6Eq20BetaDerivativeCoefficient x L level D Q * (1+|v|)^4 :=
    hd.trans hheight
  have hG : 0 ≤ chen1973Lemma6Eq20BetaDerivativeCoefficient x L level D Q := by
    unfold chen1973Lemma6Eq20BetaDerivativeCoefficient
    have := (chen1973Lemma6Eq19I_pos x L level).le
    positivity
  apply (chen1973Lemma6B_le_moment_product x L level B k m H _).trans
  calc
    _ ≤ Real.sqrt (9 * chen1973Lemma6Eq19SharpConstant * chen1973Lemma6Eq19I x L level /
        Real.log x ^ 2 * ((Q : ℝ) + ((B*2^k : ℕ) : ℝ)/D) *
        ((B*2^k : ℕ) : ℝ)^(1-2*chen1973Lemma6Beta x)) * Real.sqrt (Real.sqrt
        (chen1973Lemma6Eq20BetaDerivativeCoefficient x L level D Q * (1+|v|)^4) *
        Real.sqrt (chen1973Lemma6Eq19I x L level *
          (chen1973Lemma6Eq19SharpConstant * ((Q : ℝ) + ((H*H : ℕ) : ℝ)/D) *
          (1+Real.log (H*H : ℕ))^4))) := by gcongr
    _ = _ := by
      rw [Real.sqrt_mul (Real.sqrt_nonneg _), eq20_fourth_root_height hG (by positivity)]
      unfold eq19BetaLinearCoefficient
      ring

/-- The corrected beta integral at any H; the height is not an Eq20 complement. -/
theorem eq19Beta_integrable_and_budget
    (x L level B k m H D Q : ℕ) (hx : 3 ≤ x) (hB : 0 < B)
    (hD : 0 < D) (hQ : 2 ≤ Q)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    IntegrableOn (fun v : ℝ =>
      chen1973Lemma6B x L level B k m H (chen1973Lemma6Beta x+v*I) /
        chen1973Lemma6Eq17CorrectedKernel x (chen1973Lemma6Beta x+v*I)) (Ioi 0) ∧
    chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m H ≤
      3 * Real.pi * chen1973PerronScale (x : ℝ) *
        eq19BetaLinearCoefficient x L level B k H D Q := by
  have hl : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hβ : 1/2 ≤ chen1973Lemma6Beta x := by
    unfold chen1973Lemma6Beta
    exact le_add_of_nonneg_right (by positivity)
  apply eq20_corrected_linear_integrable_and_bound hx hβ
    (show 0 ≤ eq19BetaLinearCoefficient x L level B k H D Q by
      unfold eq19BetaLinearCoefficient; positivity)
    (fun v : ℝ => chen1973Lemma6B x L level B k m H (chen1973Lemma6Beta x+v*I))
    (chen1973Lemma6B_eq20_beta_continuous hD hcell)
  · intro v hv
    unfold chen1973Lemma6B
    positivity
  · intro v hv
    simpa only [abs_of_pos (mem_Ioi.mp hv)] using
      eq19Beta_actual_linear x L level B k m H D Q hx hB hD hQ hcell v

/-- The large-Y cutoff is a consequence of the actual carrier, never an extra assumption. -/
theorem eq19Beta_nonempty_pairD_bound {x B k m : ℕ} (hx : 3 ≤ x)
    (hne : (chen1973Lemma6PrimePairShell x B k m).Nonempty) :
    ((B*2^k : ℕ) : ℝ) ≤ (x : ℝ)^((2 : ℝ)/3) := by
  obtain ⟨pp, hpp⟩ := hne
  have hp := (Finset.mem_Ioc.mp (chen1973Lemma6_eq19_dyadic_pair_product_mem hpp)).1
  obtain ⟨hp1, hp2⟩ := chen1973Lemma6PrimePairShell_pos hpp
  have hprod : (0 : ℝ) < (pp.1 : ℝ)*pp.2 := by positivity
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hy := (chen1973Lemma6_eq21_primeRegion_log_y hx
    (chen1973Lemma6_eq21_actualShell_subset_primeRegion x B k m hpp)).2
  rw [Real.log_div hx0.ne' hprod.ne'] at hy
  have hlog : Real.log ((pp.1 : ℝ)*pp.2) ≤ Real.log ((x : ℝ)^((2 : ℝ)/3)) := by
    rw [Real.log_rpow hx0]
    linarith
  have hprod_le : (pp.1 : ℝ)*pp.2 ≤ (x : ℝ)^((2 : ℝ)/3) :=
    (Real.log_le_log_iff hprod (by positivity)).mp hlog
  exact (show ((B*2^k : ℕ) : ℝ) ≤ (pp.1 : ℝ)*pp.2 by exact_mod_cast hp.le).trans hprod_le

/-- Empty shells give the literal zero numerator and corrected integral. -/
theorem eq19Beta_empty_integral {x L level B k m H : ℕ}
    (he : chen1973Lemma6PrimePairShell x B k m = ∅) :
    chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m H = 0 := by
  simp [chen1973Lemma6Eq20CorrectedSecondIntegral, chen1973Lemma6B, he]

/-- The source cut gives the cap required by the already verified alpha endpoint. -/
lemma eq19Beta_source_cap {x L B lastD level k : ℕ} {ε : ℝ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k) (hε : 0 ≤ ε)
    (hcut : (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε))
    (hQ : chen1973Lemma6Eq19SourceQ L level ≤ 2*lastD) :
    (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1:ℝ)/2) := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by have := P.hx; omega)
  have hp := Real.rpow_le_rpow_of_exponent_le hx1 (show (1:ℝ)/2-ε ≤ 1/2 by linarith)
  have hQr : (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ 2*(lastD : ℝ) := by exact_mod_cast hQ
  linarith

/-- Uniform subpower control of the printed exponential, with threshold before level. -/
lemma eq19Beta_Ilx_subpower (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ L B lastD level k : ℕ,
      Chen1973Lemma6Eq19SourceParameters x L B lastD level k →
      chen1973Lemma6Eq19SourceQ L level ≤ 2*lastD →
      (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1:ℝ)/2) →
      chen1973Lemma6Equation20Ilx x level ≤ (x : ℝ)^η := by
  refine ⟨Real.exp (Real.exp (Real.exp (24/η))), ?_⟩
  intro x hx L B lastD level k P hQ hcap
  let R := eq19AlphaQ0 x level
  let u := Real.log (x : ℝ)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by have := P.hx; omega)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by have := P.hx; omega)
  have hu : 1 ≤ u := P.hlog_one
  have hu0 : 0 < u := by linarith
  have hRlow : u^100 ≤ R :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hup : u ≤ u^100 := by
    simpa using pow_le_pow_right₀ hu (show 1 ≤ (100:ℕ) by omega)
  have huR : u ≤ R := hup.trans hRlow
  have hR0 : 0 < R := hu0.trans_le huR
  have hloglog : 24/η ≤ Real.log (Real.log R) := by
    have h1 : Real.exp (Real.exp (24/η)) ≤ u := by
      simpa [u] using Real.log_le_log (Real.exp_pos _) hx
    have h2 : Real.exp (24/η) ≤ Real.log R := by
      simpa using Real.log_le_log (Real.exp_pos _) (h1.trans huR)
    simpa using Real.log_le_log (Real.exp_pos _) h2
  have hll0 : 0 < Real.log (Real.log R) := (by positivity : 0 < 24/η).trans_le hloglog
  have hR4 : R ≤ 4*x := by
    have hg := (eq19Alpha_source_geometry P hQ).2.2.2
    have hs : (x : ℝ)^((1:ℝ)/2) ≤ x := by
      simpa using Real.rpow_le_rpow_of_exponent_le hx1 (show (1:ℝ)/2 ≤ 1 by norm_num)
    dsimp [R]
    linarith
  have hlogR : Real.log R ≤ 4*u := by
    have hh := Real.log_le_log hR0 hR4
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hx0.ne'] at hh
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    dsimp [u] at *
    linarith
  have hpay : 6*Real.log R / Real.log (Real.log R) ≤ η*u := by
    apply (div_le_iff₀ hll0).mpr
    have h24 : 24 ≤ η*Real.log (Real.log R) := by
      simpa [mul_comm] using (div_le_iff₀ hη).mp hloglog
    nlinarith [mul_le_mul_of_nonneg_right h24 hu0.le]
  have heq : chen1973Lemma6Equation20Ilx x level =
      Real.exp (6*Real.log R / Real.log (Real.log R)) := by
    simp [chen1973Lemma6Equation20Ilx, R, eq19AlphaQ0, Real.rpow_natCast]
  rw [heq, Real.rpow_def_of_pos hx0]
  exact Real.exp_le_exp.mpr (by simpa [u, mul_comm] using hpay)

/-- Upper height budget at the actual ceil, not the obsolete W-height. -/
lemma eq19Beta_printedHeight_upper {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k)
    (hQ : chen1973Lemma6Eq19SourceQ L level ≤ 2*lastD)
    (htt : 60 ≤ Real.log (Real.log (eq19AlphaQ0 x level))) :
    (chen1973Lemma6Eq19PrintedHeight x level : ℝ) ≤
      4*(chen1973Lemma6Eq19SourceQ L level : ℝ)*Real.log x^100*
        chen1973Lemma6Equation20Ilx x level := by
  let R := eq19AlphaQ0 x level
  let u := Real.log (x : ℝ)
  let J := chen1973Lemma6Equation20Ilx x level
  have hJ : 1 ≤ J := (eq19Alpha_I_log90 P.hlog_one htt).1
  have hu : 1 ≤ u := P.hlog_one
  have hR : 1 ≤ R := by
    apply le_trans (one_le_pow₀ hu : 1 ≤ u^100)
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hT : 1 ≤ R*u^100*J :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hR (one_le_pow₀ hu)) hJ
  have hTeq : chen1973Lemma6Eq19PrintedHeightReal x level = R*u^100*J := by
    dsimp [R, u, J, eq19AlphaQ0, chen1973Lemma6Eq19PrintedHeightReal]
    ring
  have hc : (chen1973Lemma6Eq19PrintedHeight x level : ℝ) < R*u^100*J+1 := by
    change (⌈chen1973Lemma6Eq19PrintedHeightReal x level⌉₊ : ℝ) < _
    rw [hTeq]
    exact Nat.ceil_lt_add_one (by linarith)
  have hg : R ≤ 2*(chen1973Lemma6Eq19SourceQ L level : ℝ) :=
    (eq19Alpha_source_geometry P hQ).2.2.2
  have hm := mul_le_mul_of_nonneg_right hg
    (show 0 ≤ u^100*J by
      have : 0 ≤ J := by linarith
      positivity)
  dsimp [u, J] at *
  nlinarith

def eq19BetaDerivativeConstant : ℝ := 32*21000000*9*8^4*16

def eq19BetaMobiusConstant : ℝ := 33*241^4*chen1973Lemma6Eq19SharpConstant

def eq19BetaNumeratorConstant : ℝ := Real.sqrt
  (18*chen1973Lemma6Eq19SharpConstant * Real.sqrt
    (eq19BetaMobiusConstant*eq19BetaDerivativeConstant))

lemma eq19Beta_derivative_coefficient {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k)
    (hQ : chen1973Lemma6Eq19SourceQ L level ≤ 2*lastD)
    (hlogQ : Real.log (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ 4*Real.log x) :
    chen1973Lemma6Eq20BetaDerivativeCoefficient x L level
      (chen1973Lemma6Eq19SourceD L level) (chen1973Lemma6Eq19SourceQ L level) ≤
      eq19BetaDerivativeConstant * chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6Eq19SourceQ L level : ℝ) * Real.log x^8 := by
  let u := Real.log (x : ℝ)
  let Q : ℝ := chen1973Lemma6Eq19SourceQ L level
  let D : ℝ := chen1973Lemma6Eq19SourceD L level
  let W := chen1973Lemma6Eq19I x L level
  let r := 1/(2*u)
  let a := 1+|chen1973Lemma6Beta x|+r
  have hu : 1 ≤ u := P.hlog_one
  have hu0 : 0 < u := by linarith
  have hD : 0 < D := by dsimp [D]; exact_mod_cast chen1973Lemma6Eq19SourceD_pos P
  have hQ0 : 0 < Q := by dsimp [Q]; exact_mod_cast chen1973Lemma6Eq19SourceQ_pos P
  have hW : 0 ≤ W := (chen1973Lemma6Eq19I_pos x L level).le
  have hQD : Q = 2*D := by dsimp [Q,D]; exact_mod_cast (eq19Alpha_source_geometry P hQ).1
  have hinv : 1/u ≤ 1 := (div_le_iff₀ hu0).mpr (by linarith)
  have hβ : 0 ≤ chen1973Lemma6Beta x := by unfold chen1973Lemma6Beta; positivity
  have ha : 0 ≤ a := by dsimp [a, r]; positivity
  have ha3 : a ≤ 3 := by
    dsimp only [a, r]
    rw [abs_of_nonneg hβ]
    change 1 + (1/2+1/u) + 1/(2*u) ≤ 3
    have hi : 1/(2*u) = (1/u)/2 := by ring
    rw [hi]
    linarith
  have hbase : 1 ≤ Q*(1+a) := by
    have hQ1 : 1 ≤ Q := by
      dsimp [Q]
      exact_mod_cast (show 1 ≤ chen1973Lemma6Eq19SourceQ L level by have := chen1973Lemma6Eq19SourceQ_ge_two P; omega)
    exact one_le_mul_of_one_le_of_one_le hQ1 (le_add_of_nonneg_right ha)
  have hlog0 : 0 ≤ 1+Real.log (Q*(1+a)) := by linarith [Real.log_nonneg hbase]
  have hlog : 1+Real.log (Q*(1+a)) ≤ 8*u := by
    have hh : Real.log (Q*(1+a)) ≤ Real.log (Q*4) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul hQ0.ne' (by norm_num : (4:ℝ) ≠ 0)] at hh
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    change Real.log Q ≤ 4*u at hlogQ
    linarith
  change 16*21000000*W*Q^2*a^2*(1+Real.log (Q*(1+a)))^4/(D*r^4) ≤ _
  calc
    _ ≤ 16*21000000*W*Q^2*3^2*(8*u)^4/(D*r^4) := by gcongr
    _ = eq19BetaDerivativeConstant*W*Q*u^8 := by
      dsimp [eq19BetaDerivativeConstant, r]
      rw [hQD]
      field_simp
      ring

lemma eq19Beta_mobius_coefficient {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k)
    (hQ : chen1973Lemma6Eq19SourceQ L level ≤ 2*lastD)
    (hcap : (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1:ℝ)/2))
    (htt : 60 ≤ Real.log (Real.log (eq19AlphaQ0 x level))) :
    let H := chen1973Lemma6Eq19PrintedHeight x level
    chen1973Lemma6Eq19I x L level *
      (chen1973Lemma6Eq19SharpConstant *
        ((chen1973Lemma6Eq19SourceQ L level : ℝ) + ((H*H : ℕ) : ℝ)/chen1973Lemma6Eq19SourceD L level) *
        (1+Real.log (H*H : ℕ))^4) ≤
    eq19BetaMobiusConstant * chen1973Lemma6Eq19I x L level *
      (chen1973Lemma6Eq19SourceQ L level : ℝ) * Real.log x^204 *
        chen1973Lemma6Equation20Ilx x level^2 := by
  dsimp only
  let u := Real.log (x : ℝ)
  let Q : ℝ := chen1973Lemma6Eq19SourceQ L level
  let D : ℝ := chen1973Lemma6Eq19SourceD L level
  let H := chen1973Lemma6Eq19PrintedHeight x level
  let J := chen1973Lemma6Equation20Ilx x level
  let W := chen1973Lemma6Eq19I x L level
  have hu : 1 ≤ u := P.hlog_one
  have hJ : 1 ≤ J := (eq19Alpha_I_log90 P.hlog_one htt).1
  have hD : 0 < D := by dsimp [D]; exact_mod_cast chen1973Lemma6Eq19SourceD_pos P
  have hQ0 : 0 < Q := by dsimp [Q]; exact_mod_cast chen1973Lemma6Eq19SourceQ_pos P
  have hQD : Q = 2*D := by dsimp [Q,D]; exact_mod_cast (eq19Alpha_source_geometry P hQ).1
  have hW : 0 ≤ W := (chen1973Lemma6Eq19I_pos x L level).le
  have hC := chen1973Lemma6_eq19SharpConstant_pos.le
  obtain ⟨hH2, hlogH, _⟩ := eq19Alpha_printedHeight_logs P hQ hcap htt
  have hH0 : (0:ℝ) < H := by exact_mod_cast (show 0 < H by dsimp [H]; omega)
  have hHup : (H:ℝ) ≤ 4*Q*u^100*J := eq19Beta_printedHeight_upper P hQ htt
  have hlogh : Real.log (H:ℝ) ≤ 120*u := by
    have hh : Real.log (H:ℝ) ≤ Real.log (H+1 : ℕ) := Real.log_le_log hH0 (by push_cast; linarith)
    change 1+Real.log (H+1 : ℕ) ≤ 120*u at hlogH
    linarith
  have hlog2 : 1+Real.log (H*H : ℕ) ≤ 241*u := by
    rw [Nat.cast_mul, Real.log_mul hH0.ne' hH0.ne']
    linarith
  have hlog20 : 0 ≤ 1+Real.log (H*H : ℕ) := by
    have hH1 : (1:ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by dsimp [H]; omega)
    have h1 : (1:ℝ) ≤ (H*H : ℕ) := by push_cast; nlinarith
    linarith [Real.log_nonneg h1]
  have hgeom : Q+(H:ℝ)^2/D ≤ 33*Q*u^200*J^2 := by
    have hp : (H:ℝ)^2 ≤ (4*Q*u^100*J)^2 := by gcongr
    have hup : 1 ≤ u^200*J^2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hu) (one_le_pow₀ hJ)
    apply (mul_le_mul_iff_left₀ hD).mp
    calc
      (Q+(H:ℝ)^2/D)*D = Q*D+(H:ℝ)^2 := by field_simp
      _ ≤ Q*D+(4*Q*u^100*J)^2 := by linarith
      _ ≤ (33*Q*u^200*J^2)*D := by
        have hh := mul_le_mul_of_nonneg_left hup (show 0 ≤ Q*D by positivity)
        rw [hQD] at *
        nlinarith
  change W*(chen1973Lemma6Eq19SharpConstant*(Q+((H*H:ℕ):ℝ)/D)*(1+Real.log (H*H:ℕ))^4) ≤ _
  calc
    _ ≤ W*(chen1973Lemma6Eq19SharpConstant*(33*Q*u^200*J^2)*(241*u)^4) := by
      push_cast at hlog20 hlog2 ⊢
      gcongr
      simpa [pow_two] using hgeom
    _ = eq19BetaMobiusConstant*W*Q*u^204*J^2 := by
      unfold eq19BetaMobiusConstant
      ring

/-- Algebraic joining of pair², S⁴ and L'⁴ preserves the square-root conductor scale. -/
lemma eq19Beta_three_roots {A C₁ C₂ W Q D Y u J : ℝ}
    (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hW : 0 ≤ W) (hQ : 0 ≤ Q) (hD : 0 < D) (hY : 0 ≤ Y)
    (hu : 0 ≤ u) (hJ : 0 ≤ J) (hQD : Q = 2*D) :
    Real.sqrt (A*W*(Q+Y/D)) *
      Real.sqrt (Real.sqrt (C₁*W*Q*u^204*J^2)) *
      Real.sqrt (Real.sqrt (C₂*W*Q*u^8)) ≤
    Real.sqrt (2*A*Real.sqrt (C₁*C₂))*W*Real.sqrt J*(Q+Real.sqrt Y)*u^53 := by
  let F := C₁*W*Q*u^204*J^2
  let G := C₂*W*Q*u^8
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hFG : Real.sqrt (F*G) = Real.sqrt (C₁*C₂)*W*Q*u^106*J := by
    rw [show F*G = (C₁*C₂)*(W*Q*u^106*J)^2 by dsimp [F,G]; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring
  have hgeom : Q*(Q+Y/D) ≤ 2*(Q+Real.sqrt Y)^2 := by
    have heq : Q*(Q+Y/D) = Q^2+2*Y := by rw [hQD]; field_simp
    rw [heq]
    nlinarith [Real.sq_sqrt hY, Real.sqrt_nonneg Y, mul_nonneg hQ (Real.sqrt_nonneg Y)]
  calc
    _ = Real.sqrt (A*W*(Q+Y/D)) * Real.sqrt (Real.sqrt (F*G)) := by
      rw [Real.sqrt_mul hF, Real.sqrt_mul (Real.sqrt_nonneg F)]
      ring
    _ = Real.sqrt (A*Real.sqrt (C₁*C₂)*W^2*J*u^106*(Q*(Q+Y/D))) := by
      rw [hFG, ← Real.sqrt_mul (by positivity)]
      congr 1
      ring
    _ ≤ Real.sqrt (2*A*Real.sqrt (C₁*C₂))*W*Real.sqrt J*(Q+Real.sqrt Y)*u^53 := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      calc
        _ ≤ A*Real.sqrt (C₁*C₂)*W^2*J*u^106*(2*(Q+Real.sqrt Y)^2) := by gcongr
        _ = _ := by
          simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*A*Real.sqrt (C₁*C₂)),
            Real.sq_sqrt hJ]
          ring

/-- Source-faithful scalar numerator coefficient at the printed height. -/
lemma eq19Beta_printed_coefficient {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k)
    (hQ : chen1973Lemma6Eq19SourceQ L level ≤ 2*lastD)
    (hcap : (chen1973Lemma6Eq19SourceQ L level : ℝ) ≤ 2*(x : ℝ)^((1:ℝ)/2))
    (htt : 60 ≤ Real.log (Real.log (eq19AlphaQ0 x level))) :
    eq19BetaLinearCoefficient x L level B k (chen1973Lemma6Eq19PrintedHeight x level)
      (chen1973Lemma6Eq19SourceD L level) (chen1973Lemma6Eq19SourceQ L level) ≤
    eq19BetaNumeratorConstant * chen1973Lemma6Eq19I x L level *
      Real.sqrt (chen1973Lemma6Equation20Ilx x level) *
      ((chen1973Lemma6Eq19SourceQ L level : ℝ)+Real.sqrt ((B*2^k : ℕ) : ℝ)) *
      Real.log x^53 := by
  let u := Real.log (x : ℝ)
  let Q : ℝ := chen1973Lemma6Eq19SourceQ L level
  let D : ℝ := chen1973Lemma6Eq19SourceD L level
  let Y : ℝ := (B*2^k : ℕ)
  let H := chen1973Lemma6Eq19PrintedHeight x level
  let J := chen1973Lemma6Equation20Ilx x level
  let W := chen1973Lemma6Eq19I x L level
  have hu : 1 ≤ u := P.hlog_one
  have hu0 : 0 < u := by linarith
  have hW : 0 ≤ W := (chen1973Lemma6Eq19I_pos x L level).le
  have hD : 0 < D := by dsimp [D]; exact_mod_cast chen1973Lemma6Eq19SourceD_pos P
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hQD : Q = 2*D := by dsimp [Q,D]; exact_mod_cast (eq19Alpha_source_geometry P hQ).1
  have hJ : 0 ≤ J := zero_le_one.trans (eq19Alpha_I_log90 P.hlog_one htt).1
  have hY : 1 ≤ Y := by
    dsimp [Y]
    exact_mod_cast (show 1 ≤ B*2^k from Nat.mul_pos P.hB (pow_pos (by omega) k))
  have hβ : 1/2 ≤ chen1973Lemma6Beta x := by
    unfold chen1973Lemma6Beta
    exact le_add_of_nonneg_right (by positivity)
  have hp : Y^(1-2*chen1973Lemma6Beta x) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hY (show 1-2*chen1973Lemma6Beta x ≤ 0 by linarith)
  have hC := chen1973Lemma6_eq19SharpConstant_pos.le
  have hpair : 9*chen1973Lemma6Eq19SharpConstant*W/u^2*(Q+Y/D)*
      Y^(1-2*chen1973Lemma6Beta x) ≤ 9*chen1973Lemma6Eq19SharpConstant*W*(Q+Y/D) := by
    calc
      _ ≤ 9*chen1973Lemma6Eq19SharpConstant*W/u^2*(Q+Y/D)*1 := by gcongr
      _ = (9*chen1973Lemma6Eq19SharpConstant*W*(Q+Y/D))/u^2 := by ring
      _ ≤ _ := div_le_self (by positivity) (one_le_pow₀ hu)
  have hmob := eq19Beta_mobius_coefficient P hQ hcap htt
  have hder := eq19Beta_derivative_coefficient P hQ (eq19Alpha_printedHeight_logs P hQ hcap htt).2.2
  have hC₁ : 0 ≤ eq19BetaMobiusConstant := by unfold eq19BetaMobiusConstant; positivity
  have hC₂ : 0 ≤ eq19BetaDerivativeConstant := by unfold eq19BetaDerivativeConstant; positivity
  have hroot := eq19Beta_three_roots (A := 9*chen1973Lemma6Eq19SharpConstant) (Y := Y)
    (show 0 ≤ 9*chen1973Lemma6Eq19SharpConstant by positivity)
    hC₁ hC₂ hW hQ0 hD (by dsimp [Y]; positivity) hu0.le hJ hQD
  rw [show 2*(9*chen1973Lemma6Eq19SharpConstant) = 18*chen1973Lemma6Eq19SharpConstant by ring] at hroot
  apply le_trans _ hroot
  unfold eq19BetaLinearCoefficient
  gcongr

/-- Fixed log-power absorption, quantified before every cell parameter. -/
lemma eq19Beta_log75_eventually (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → Real.log x^75 ≤ x^η := by
  have hh := (isLittleO_log_rpow_rpow_atTop (75:ℝ) hη).bound (by norm_num : (0:ℝ)<1)
  have hev : ∀ᶠ x : ℝ in Filter.atTop, Real.log x^75 ≤ x^η := by
    filter_upwards [hh, Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
    rw [show (Real.log x)^(75:ℝ) = (Real.log x)^(75:ℕ) from Real.rpow_natCast _ _] at hx
    have hb : |(Real.log x)^(75:ℕ)| ≤ x^η := by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul] using hx
    exact (le_abs_self _).trans hb
  exact Filter.eventually_atTop.mp hev

/-- Both conductor and nonempty-pair scales retain a strict power margin. -/
lemma eq19Beta_gap_scalar {x Q Y J u ε : ℝ}
    (hx : 1 ≤ x) (hu : 1 ≤ u) (hε : 0 < ε) (hεu : ε < 1/10)
    (_hJ : 0 ≤ J) (hQ : 0 ≤ Q) (_hY : 0 ≤ Y)
    (hJup : J ≤ x^(ε/4)) (hQup : Q ≤ 2*x^((1:ℝ)/2-ε))
    (hYup : Y ≤ x^((2:ℝ)/3)) (hlog : u^75 ≤ x^(ε/4)) :
    x^((1:ℝ)/2)*J*(Q+Real.sqrt Y)*u^55 ≤ 3*x/u^20 := by
  have hx0 : 0 < x := by linarith
  have hu0 : 0 < u := by linarith
  have hs : Real.sqrt Y ≤ x^((1:ℝ)/3) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    convert hYup using 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hpow1 : x^((1:ℝ)/2)*x^(ε/4)*x^((1:ℝ)/2-ε)*x^(ε/4) = x^(1-ε/2) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  have hpow2 : x^((1:ℝ)/2)*x^(ε/4)*x^((1:ℝ)/3)*x^(ε/4) = x^((5:ℝ)/6+ε/2) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  have hp1 : x^(1-ε/2) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (show 1-ε/2 ≤ 1 by linarith)
  have hp2 : x^((5:ℝ)/6+ε/2) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (show (5:ℝ)/6+ε/2 ≤ 1 by linarith)
  apply (le_div_iff₀ (pow_pos hu0 20)).mpr
  calc
    _ = x^((1:ℝ)/2)*J*(Q+Real.sqrt Y)*u^75 := by ring
    _ ≤ x^((1:ℝ)/2)*x^(ε/4)*(2*x^((1:ℝ)/2-ε)+x^((1:ℝ)/3))*x^(ε/4) := by gcongr
    _ = 2*x^(1-ε/2)+x^((5:ℝ)/6+ε/2) := by
      calc
        _ = 2*(x^((1:ℝ)/2)*x^(ε/4)*x^((1:ℝ)/2-ε)*x^(ε/4))+
          (x^((1:ℝ)/2)*x^(ε/4)*x^((1:ℝ)/3)*x^(ε/4)) := by ring
        _ = _ := by rw [hpow1, hpow2]
    _ ≤ 3*x := by linarith

/-- Printed-height beta smallness for every source cell; no hypothesis bounds Y. -/
theorem chen1973Lemma6_eq19_beta_contribution_small (ε : ℝ) (hε : 0 < ε) (hεu : ε < 1/10) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) →
      ∀ L B lastD level k m : ℕ,
      Chen1973Lemma6Eq19SourceParameters x L B lastD level k →
      (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε) →
      chen1973Lemma6Eq19SourceQ L level ≤ 2*lastD →
      2*(x : ℝ)^((1:ℝ)/2)*
        chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m
          (chen1973Lemma6Eq19PrintedHeight x level) ≤ C*x/Real.log x^20 := by
  obtain ⟨X₁, hX₁⟩ := eq19Alpha_loglog_eventually
  obtain ⟨X₂, hX₂⟩ := chen1973Lemma6_actual_W_sq_le_Ilx_eventually
  obtain ⟨X₃, hX₃⟩ := eq19Beta_Ilx_subpower (ε/4) (by positivity)
  obtain ⟨X₄, hX₄⟩ := eq19Beta_log75_eventually (ε/4) (by positivity)
  have hK : 0 < eq19BetaNumeratorConstant := by
    unfold eq19BetaNumeratorConstant eq19BetaMobiusConstant eq19BetaDerivativeConstant
    have := chen1973Lemma6_eq19SharpConstant_pos
    positivity
  refine ⟨18*Real.pi*eq19BetaNumeratorConstant, by positivity,
    max (max X₁ X₂) (max X₃ X₄), ?_⟩
  intro x hx L B lastD level k m P hcut hQ
  obtain ⟨hx₁₂, hx₃₄⟩ := max_le_iff.mp hx
  obtain ⟨hx₁, hx₂⟩ := max_le_iff.mp hx₁₂
  obtain ⟨hx₃, hx₄⟩ := max_le_iff.mp hx₃₄
  by_cases he : chen1973Lemma6PrimePairShell x B k m = ∅
  · rw [eq19Beta_empty_integral he, mul_zero]
    positivity
  have hYup := eq19Beta_nonempty_pairD_bound P.hx (Finset.nonempty_iff_ne_empty.mpr he)
  have hcap := eq19Beta_source_cap P hε.le hcut hQ
  have htt := (hX₁ x hx₁ level).2
  have hJup := hX₃ x hx₃ L B lastD level k P hQ hcap
  have hlog := hX₄ (x:ℝ) hx₄
  let u := Real.log (x:ℝ)
  let Q : ℝ := chen1973Lemma6Eq19SourceQ L level
  let J := chen1973Lemma6Equation20Ilx x level
  let W := chen1973Lemma6Eq19I x L level
  let Y : ℝ := (B*2^k : ℕ)
  have hu : 1 ≤ u := P.hlog_one
  have hu0 : 0 < u := by linarith
  have hW : 0 ≤ W := (chen1973Lemma6Eq19I_pos x L level).le
  have hJ : 0 ≤ J := zero_le_one.trans (eq19Alpha_I_log90 P.hlog_one htt).1
  have hWJ : W*Real.sqrt J ≤ J := by
    have hWI : W^2 ≤ J := hX₂ x hx₂ L level P.hL_lower
    have hWs : W ≤ Real.sqrt J := Real.le_sqrt_of_sq_le hWI
    calc
      _ ≤ Real.sqrt J*Real.sqrt J := mul_le_mul_of_nonneg_right hWs (Real.sqrt_nonneg _)
      _ = J := Real.mul_self_sqrt hJ
  have hQup : Q ≤ 2*(x:ℝ)^((1:ℝ)/2-ε) := by
    have hh : Q ≤ 2*(lastD:ℝ) := by dsimp [Q]; exact_mod_cast hQ
    linarith
  have hscalar := eq19Beta_gap_scalar
    (show (1:ℝ) ≤ x by exact_mod_cast (show 1 ≤ x by have := P.hx; omega)) hu hε hεu
    hJ (show 0 ≤ Q by dsimp [Q]; positivity) (show 0 ≤ Y by dsimp [Y]; positivity)
    hJup hQup hYup hlog
  have hcoef := eq19Beta_printed_coefficient P hQ hcap htt
  have hi := (eq19Beta_integrable_and_budget x L level B k m
    (chen1973Lemma6Eq19PrintedHeight x level)
    (chen1973Lemma6Eq19SourceD L level) (chen1973Lemma6Eq19SourceQ L level)
    P.hx P.hB (chen1973Lemma6Eq19SourceD_pos P) (chen1973Lemma6Eq19SourceQ_ge_two P)
    (chen1973Lemma6_eq19_conductorBlock_subset_source_Ioc P)).2
  have hscale : chen1973PerronScale (x:ℝ) ≤ u^2 := by
    unfold chen1973PerronScale
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
  calc
    _ ≤ 2*(x:ℝ)^((1:ℝ)/2)*(3*Real.pi*chen1973PerronScale (x:ℝ)*
        eq19BetaLinearCoefficient x L level B k (chen1973Lemma6Eq19PrintedHeight x level)
          (chen1973Lemma6Eq19SourceD L level) (chen1973Lemma6Eq19SourceQ L level)) := by gcongr
    _ ≤ 2*(x:ℝ)^((1:ℝ)/2)*(3*Real.pi*u^2*
        (eq19BetaNumeratorConstant*W*Real.sqrt J*(Q+Real.sqrt Y)*u^53)) := by
      gcongr
      unfold eq19BetaLinearCoefficient
      positivity
    _ = 6*Real.pi*eq19BetaNumeratorConstant*
        ((x:ℝ)^((1:ℝ)/2)*(W*Real.sqrt J)*(Q+Real.sqrt Y)*u^55) := by ring
    _ ≤ 6*Real.pi*eq19BetaNumeratorConstant*
        ((x:ℝ)^((1:ℝ)/2)*J*(Q+Real.sqrt Y)*u^55) := by gcongr
    _ ≤ 6*Real.pi*eq19BetaNumeratorConstant*(3*x/u^20) := by gcongr
    _ = _ := by dsimp [u]; ring

/-- The positive Eq19 cell, now with both actual corrected integrals paid. -/
theorem chen1973Lemma6_equation19_actual_cell_small (ε : ℝ) (hε : 0 < ε) (hεu : ε < 1/10) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) →
      ∀ L B lastD level k m : ℕ,
      Chen1973Lemma6Eq19SourceParameters x L B lastD level k →
      (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε) →
      chen1973Lemma6Eq19SourceQ L level ≤ 2*lastD →
      chen1973Lemma6NmBlockActual x L level B k m ≤ C*x/Real.log x^20 := by
  obtain ⟨Cα, hCα, Xα, hXα⟩ := chen1973Lemma6_equation19_small_alpha_actual_beta
  obtain ⟨Cβ, hCβ, Xβ, hXβ⟩ := chen1973Lemma6_eq19_beta_contribution_small ε hε hεu
  refine ⟨Cα+Cβ, by positivity, max Xα Xβ, ?_⟩
  intro x hx L B lastD level k m P hcut hQ
  have ha := hXα x ((le_max_left Xα Xβ).trans hx) L B lastD level k m P hQ
    (eq19Beta_source_cap P hε.le hcut hQ)
  have hb := hXβ x ((le_max_right Xα Xβ).trans hx) L B lastD level k m P hcut hQ
  calc
    _ ≤ Cα*x/Real.log x^20+2*(x:ℝ)^((1:ℝ)/2)*
      chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m
        (chen1973Lemma6Eq19PrintedHeight x level) := ha
    _ ≤ Cα*x/Real.log x^20+Cβ*x/Real.log x^20 := add_le_add le_rfl hb
    _ = _ := by ring

end AnalyticNumberTheory.LargeSieve
