import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21PowerLoss

noncomputable section
open Real Filter
namespace AnalyticNumberTheory.LargeSieve

/-- The complete smoothing order pays both right-line tails and finite horizontal
edges at T=u². The threshold precedes N; no finite-order scan is used. -/
theorem eq21FiniteScalar_tail_eventually (C : ℝ) (n : ℕ) (hC : 0 < C) :
    ∀ᶠ u : ℝ in atTop, ∀ N : ℕ, u ≤ (N : ℝ) →
      C * Real.exp (1 + Real.sqrt u) *
        (u ^ ((11 : ℝ)/10) / u^2)^N * u^n ≤ 1 := by
  have hb := (isLittleO_pow_exp_pos_mul_atTop n (by norm_num : (0:ℝ) < 1/2)).bound
    (show 0 < 1/C by positivity)
  have hl := Real.tendsto_log_atTop.eventually_ge_atTop 3
  filter_upwards [hb, hl, eventually_ge_atTop (16:ℝ)] with u hb hl hu
  intro N hN
  have hu0 : 0 < u := by linarith
  have hp : C*u^n ≤ Real.exp (u/2) := by
    change ‖u^n‖ ≤ (1/C)*‖Real.exp ((1/2)*u)‖ at hb
    rw [Real.norm_of_nonneg (pow_nonneg hu0.le n),
      Real.norm_of_nonneg (Real.exp_nonneg _)] at hb
    have hh : u^n ≤ Real.exp (u/2) / C := by
      simpa [div_eq_mul_inv, mul_comm] using hb
    simpa only [mul_comm] using (le_div_iff₀ hC).mp hh
  have hs := Real.sq_sqrt hu0.le
  have hs0 := Real.sqrt_nonneg u
  have hs4 : 4 ≤ Real.sqrt u :=
    Real.le_sqrt_of_sq_le (by norm_num; exact hu)
  have hsquare : 1+Real.sqrt u ≤ u/2 := by
    nlinarith only [hs, hs4, mul_nonneg hs0 (sub_nonneg.mpr hs4)]
  have hratio : u ^ ((11:ℝ)/10) / u^2 ≤ Real.exp (-2) := by
    have he : u^2 = Real.exp (2*Real.log u) := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using (Real.exp_log (pow_pos hu0 2)).symm
    rw [Real.rpow_def_of_pos hu0, he, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    linarith
  have hpow : (u ^ ((11:ℝ)/10) / u^2)^N ≤ Real.exp (-2*u) := by
    calc
      _ ≤ (Real.exp (-2))^N := pow_le_pow_left₀ (by positivity) hratio N
      _ = Real.exp (-2*(N:ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  calc
    _ = (C*u^n)*Real.exp (1+Real.sqrt u)*(u ^ ((11:ℝ)/10) / u^2)^N := by ring
    _ ≤ Real.exp (u/2)*Real.exp (u/2)*Real.exp (-2*u) := by
      gcongr
    _ = Real.exp (-u) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)

/-- Tail payment uses the actual Perron floor, uniformly before all cells. -/
theorem chen1973Lemma6_eq21_finite_tail_eventually
    (C : ℝ) (n : ℕ) (hC : 0 < C) :
    ∀ᶠ x : ℕ in atTop,
      C * Real.exp (1 + Real.sqrt (Real.log (x:ℝ))) *
        (chen1973PerronScale (x:ℝ) / Real.log (x:ℝ)^2)^
          (chen1973PerronOrder (x:ℝ)+1) * Real.log (x:ℝ)^n ≤ 1 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eq21FiniteScalar_tail_eventually C n hC)] with x hx
  apply hx (chen1973PerronOrder (x:ℝ)+1)
  simpa [chen1973PerronOrder] using (Nat.lt_floor_add_one (Real.log (x:ℝ))).le

/-- The finite-disk derivative bound after the conductor cap. -/
def eq21FiniteScalarMbar (u : ℝ) : ℝ :=
  20 * Real.sqrt u * (Real.log 32 + (205:ℝ)/2 * Real.log u)

/-- The short left segment, unlike the right tails, needs the sharper sqrt(u)
log(u) derivative budget. Its cutoff precedes the contour real part. -/
theorem chen1973Lemma6_eq21_finite_left_budget_eventually :
    ∀ᶠ x : ℕ in atTop, ∀ σ : ℝ, (1:ℝ)/2 ≤ σ →
      eq21FiniteScalarMbar (Real.log (x:ℝ)) *
        (σ⁻¹ + Real.log (Real.log (x:ℝ)^2)) ≤ Real.log (x:ℝ)/3 := by
  let C : ℝ := 20*(Real.log 32+(205:ℝ)/2)
  have h32 : 0 ≤ Real.log (32:ℝ) := Real.log_nonneg (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlog : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [chen1973Lemma6_eq21_eventually_powerLoss_loglog_absorb
      (6*C) 2 (θ := (1:ℝ)/2) (by norm_num), hlog.eventually_ge_atTop 1] with x hp hu
  intro σ hσ
  let u := Real.log (x:ℝ)
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hlu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hsi : σ⁻¹ ≤ (2:ℝ) := by
    simpa [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/2) hσ
  have hM : eq21FiniteScalarMbar u ≤ C*Real.sqrt u*(1+Real.log u) := by
    have hh : Real.log 32+(205:ℝ)/2*Real.log u ≤
        (Real.log 32+(205:ℝ)/2)*(1+Real.log u) := by
      nlinarith only [mul_nonneg h32 hlu]
    calc
      _ ≤ 20*Real.sqrt u*((Real.log 32+(205:ℝ)/2)*(1+Real.log u)) := by
        unfold eq21FiniteScalarMbar
        gcongr
      _ = _ := by dsimp [C]; ring
  have hK : σ⁻¹+Real.log (u^2) ≤ 2*(1+Real.log u) := by
    rw [Real.log_pow]
    norm_num
    linarith
  have hK0 : 0 ≤ σ⁻¹+Real.log (u^2) := by
    have hs0 : 0 < σ := by linarith
    have hlog0 : 0 ≤ Real.log (u^2) := Real.log_nonneg (one_le_pow₀ hu)
    positivity
  have hprod : eq21FiniteScalarMbar u*(σ⁻¹+Real.log (u^2)) ≤
      2*C*Real.sqrt u*(1+Real.log u)^2 := by
    calc
      _ ≤ (C*Real.sqrt u*(1+Real.log u))*(2*(1+Real.log u)) := by gcongr
      _ = _ := by ring
  change (6*C)*u^((1:ℝ)/2)*(1+Real.log u)^2 ≤ u at hp
  rw [← Real.sqrt_eq_rpow] at hp
  change eq21FiniteScalarMbar u*(σ⁻¹+Real.log (u^2)) ≤ u/3
  linarith only [hprod, hp]

end AnalyticNumberTheory.LargeSieve
