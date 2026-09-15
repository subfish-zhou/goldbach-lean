import MathlibNt.Wu2004MeanValue.SieveAsymptotics
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

/-! Uniform Liu-normalized Mertens bounds at the literal strict real cutoff. -/

namespace Wu2004MeanValue

open Filter Finset
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
noncomputable section

def sieveDensityProduct (N : ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ siftingPrimes N z, (1 - 1 / ((p : ℝ) - 1))

theorem sieveDensityProduct_eq_goldbachSieveProduct (N : ℕ) (z : ℝ) :
    sieveDensityProduct N z = MertensTheorem.goldbachSieveProduct N ⌈z⌉₊ := rfl

theorem sieveDensityProduct_nonneg (N : ℕ) (z : ℝ) :
    0 ≤ sieveDensityProduct N z := by
  apply prod_nonneg
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast (mem_siftingPrimes.mp hp).2.1.two_le
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  exact sub_nonneg.mpr ((div_le_one hp1).mpr (by linarith))

def sieveMertensCutoff (B x : ℝ) : ℕ := ⌈sieveAsymptoticZ B x⌉₊ - 1

theorem tendsto_sieveMertensCutoff_atTop (B : ℝ) :
    Tendsto (sieveMertensCutoff B) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [(tendsto_nat_ceil_atTop.comp
    (tendsto_sieveAsymptoticZ_atTop B)).eventually (eventually_ge_atTop (n + 1))]
    with x hx
  dsimp [sieveMertensCutoff, Function.comp_def] at *
  omega

theorem sieveMertensCutoff_bounds (B : ℝ) {x : ℝ}
    (hz : 2 ≤ sieveAsymptoticZ B x) :
    sieveAsymptoticZ B x / 2 ≤ (sieveMertensCutoff B x : ℝ) ∧
      (sieveMertensCutoff B x : ℝ) ≤ sieveAsymptoticZ B x := by
  have hceil := Nat.le_ceil (sieveAsymptoticZ B x)
  have hceil' := Nat.ceil_lt_add_one (by linarith : 0 ≤ sieveAsymptoticZ B x)
  have hn : 1 ≤ ⌈sieveAsymptoticZ B x⌉₊ := by
    have : (1 : ℝ) ≤ (⌈sieveAsymptoticZ B x⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  simp only [sieveMertensCutoff, Nat.cast_sub hn, Nat.cast_one]
  constructor <;> linarith

theorem tendsto_log_sieveMertensCutoff_div_log (B : ℝ) :
    Tendsto (fun x => Real.log (sieveMertensCutoff B x : ℝ) / Real.log x)
      atTop (nhds (1 / 4 : ℝ)) := by
  have hlo : Tendsto (fun x => Real.log (sieveAsymptoticZ B x / 2) / Real.log x)
      atTop (nhds (1 / 4 : ℝ)) := by
    have h := (tendsto_log_sieveAsymptoticZ_div_log B).sub
      (Real.tendsto_log_atTop.const_div_atTop (Real.log 2))
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [(tendsto_sieveAsymptoticZ_atTop B).eventually
      (eventually_gt_atTop 0)] with x hx
    rw [Real.log_div hx.ne' (by norm_num)]
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo
    (tendsto_log_sieveAsymptoticZ_div_log B)
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      (tendsto_sieveAsymptoticZ_atTop B).eventually (eventually_ge_atTop 2)]
      with x hx hz
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by linarith : 0 < sieveAsymptoticZ B x / 2)
        (sieveMertensCutoff_bounds B hz).1) (Real.log_pos hx).le
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      (tendsto_sieveAsymptoticZ_atTop B).eventually (eventually_ge_atTop 2)]
      with x hx hz
    have hm := sieveMertensCutoff_bounds B hz
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by linarith : 0 < (sieveMertensCutoff B x : ℝ)) hm.2)
      (Real.log_pos hx).le

theorem tendsto_sieveMertensUpperCoefficient (B C : ℝ) :
    Tendsto (fun x : ℝ => Real.log x *
      (Real.exp (-Real.eulerMascheroniConstant) /
          Real.log (sieveMertensCutoff B x : ℝ) +
        C / Real.log (sieveMertensCutoff B x : ℝ) ^ 2))
      atTop (nhds (4 * Real.exp (-Real.eulerMascheroniConstant))) := by
  have hqinv := (tendsto_log_sieveMertensCutoff_div_log B).inv₀
    (by norm_num : (1 / 4 : ℝ) ≠ 0)
  have hlogm := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_sieveMertensCutoff_atTop B))
  have hloginv := tendsto_inv_atTop_zero.comp hlogm
  have h := (hqinv.const_mul (Real.exp (-Real.eulerMascheroniConstant))).add
    ((hqinv.const_mul C).mul hloginv)
  have h' : Tendsto (fun x : ℝ =>
      Real.exp (-Real.eulerMascheroniConstant) *
        (Real.log (sieveMertensCutoff B x : ℝ) / Real.log x)⁻¹ +
      (C * (Real.log (sieveMertensCutoff B x : ℝ) / Real.log x)⁻¹) *
        (Real.log (sieveMertensCutoff B x : ℝ))⁻¹)
      atTop (nhds (4 * Real.exp (-Real.eulerMascheroniConstant))) := by
    simpa [mul_comm] using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_sieveMertensCutoff_atTop B).eventually (eventually_ge_atTop 2)]
    with x hx hm
  have hmlog : 0 < Real.log (sieveMertensCutoff B x : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < sieveMertensCutoff B x))
  field_simp [(Real.log_pos hx).ne', hmlog.ne']

/-- The threshold is independent of `N`. The exact Mertens product identity
also covers `N = 2`, unlike the frozen asymptotic wrapper's redundant `4 ≤ N`. -/
theorem eventually_sieveDensityProduct_upper (B η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ, Even N → 2 ≤ N →
      sieveDensityProduct N (sieveAsymptoticZ B x) ≤
        (8 * Real.exp (-Real.eulerMascheroniConstant) + η) *
          SingularSeries.liuSingularSeries N / Real.log x := by
  let A := 4 * Real.exp (-Real.eulerMascheroniConstant)
  have hA : 0 < A := by positivity
  let d := min 1 (η / (4 * (A + 2)))
  have hd : 0 < d := lt_min (by norm_num) (div_pos hη (by positivity))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdη : d * (A + 2) ≤ η / 4 := by
    have h := min_le_right (1 : ℝ) (η / (4 * (A + 2)))
    change d ≤ η / (4 * (A + 2)) at h
    apply (le_div_iff₀ (by positivity : 0 < 4 * (A + 2))).mp at h
    nlinarith
  obtain ⟨C, hC⟩ := MertensTheorem.mertens_product_formula
  have hcoef := (tendsto_sieveMertensUpperCoefficient B C).eventually
    (Iic_mem_nhds (show A < A + d by linarith))
  have hseries := (tendsto_sieveMertensCutoff_atTop B).eventually
    (SingularSeries.eventually_liuSingularSeriesTruncated_le d hd)
  filter_upwards [hcoef, hseries, eventually_gt_atTop (1 : ℝ),
    (tendsto_sieveMertensCutoff_atTop B).eventually (eventually_ge_atTop 2)]
    with x hcoefx hseriesx hx hm N hN hN2
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hz3 : 3 ≤ ⌈sieveAsymptoticZ B x⌉₊ := by
    change 2 ≤ ⌈sieveAsymptoticZ B x⌉₊ - 1 at hm
    omega
  let T := SingularSeries.singularSeriesTruncated N (sieveMertensCutoff B x)
  let S := SingularSeries.liuSingularSeries N
  have hT : 0 < T := SingularSeries.singularSeriesTruncated_pos N _ (by omega)
  have hS : 0 < S := SingularSeries.liuSingularSeries_pos N
  have hproduct :
      sieveDensityProduct N (sieveAsymptoticZ B x) ≤
        T * (Real.exp (-Real.eulerMascheroniConstant) /
          Real.log (sieveMertensCutoff B x : ℝ) +
          C / Real.log (sieveMertensCutoff B x : ℝ) ^ 2) := by
    rw [sieveDensityProduct_eq_goldbachSieveProduct,
      MertensTheorem.sieveProduct_identity N _ (by omega) hN]
    have hbound := (abs_le.mp (hC (sieveMertensCutoff B x) hm)).2
    have hupper : MertensTheorem.primeProduct (sieveMertensCutoff B x) ≤
        Real.exp (-Real.eulerMascheroniConstant) /
          Real.log (sieveMertensCutoff B x : ℝ) +
          C / Real.log (sieveMertensCutoff B x : ℝ) ^ 2 := by linarith
    simpa only [T, sieveMertensCutoff, mul_comm] using
      mul_le_mul_of_nonneg_right hupper hT.le
  have hcoefficient :
      Real.exp (-Real.eulerMascheroniConstant) /
          Real.log (sieveMertensCutoff B x : ℝ) +
          C / Real.log (sieveMertensCutoff B x : ℝ) ^ 2 ≤
        (A + d) / Real.log x := by
    apply (le_div_iff₀ hlogx).2
    simpa [A, mul_comm] using hcoefx
  have hlegacy : T ≤ 2 * (1 + d) * S := by
    rw [show T = 2 * SingularSeries.liuSingularSeriesTruncated N
        (sieveMertensCutoff B x) from
      SingularSeries.singularSeriesTruncated_eq_two_mul_liuSingularSeriesTruncated
        N _ hN hm]
    simpa [S, mul_assoc] using
      mul_le_mul_of_nonneg_left (hseriesx N (by omega)) (by norm_num : (0 : ℝ) ≤ 2)
  have hfinal : 2 * (A + d) * (1 + d) ≤ 2 * A + η := by
    have hdsq : d ^ 2 ≤ d := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]
    nlinarith
  calc
    sieveDensityProduct N (sieveAsymptoticZ B x) ≤
        T * (Real.exp (-Real.eulerMascheroniConstant) /
          Real.log (sieveMertensCutoff B x : ℝ) +
          C / Real.log (sieveMertensCutoff B x : ℝ) ^ 2) := hproduct
    _ ≤ T * ((A + d) / Real.log x) :=
      mul_le_mul_of_nonneg_left hcoefficient hT.le
    _ ≤ (2 * (1 + d) * S) * ((A + d) / Real.log x) :=
      mul_le_mul_of_nonneg_right hlegacy (div_nonneg (by linarith) hlogx.le)
    _ = (2 * (A + d) * (1 + d)) * S / Real.log x := by ring
    _ ≤ (2 * A + η) * S / Real.log x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfinal hS.le) hlogx.le
    _ = (8 * Real.exp (-Real.eulerMascheroniConstant) + η) *
        SingularSeries.liuSingularSeries N / Real.log x := by dsimp [A, S]; ring

/-- A single positive density error works for every fixed logarithmic exponent.
The eventual quantifier precedes the unrestricted even integer `N`. -/
theorem exists_eventually_sieveDensityProduct_upperFactor (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ B : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ, Even N → 2 ≤ N →
        sieveDensityProduct N (sieveAsymptoticZ B x) *
          (jurkatRichertUpperLinearSieveFactor (sieveAsymptoticRatio B x) + ρ) ≤
            (8 + ε) * SingularSeries.liuSingularSeries N / Real.log x := by
  let A := 8 * Real.exp (-Real.eulerMascheroniConstant)
  let E := Real.exp Real.eulerMascheroniConstant
  have hA : 0 < A := by positivity
  have hE : 0 < E := Real.exp_pos _
  have hAE : A * E = 8 := by
    dsimp [A, E]
    rw [mul_assoc, ← Real.exp_add]
    norm_num
  let d := min 1 (ε / (4 * (2 * A + E + 2)))
  have hd : 0 < d := lt_min (by norm_num) (div_pos hε (by positivity))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdε : d * (2 * A + E + 2) ≤ ε / 4 := by
    have h := min_le_right (1 : ℝ) (ε / (4 * (2 * A + E + 2)))
    change d ≤ ε / (4 * (2 * A + E + 2)) at h
    apply (le_div_iff₀ (by positivity : 0 < 4 * (2 * A + E + 2))).mp at h
    nlinarith
  have hfinal : (A + d) * (E + 2 * d) ≤ 8 + ε := by
    have hdsq : d ^ 2 ≤ d := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]
    nlinarith
  refine ⟨d, hd, fun B => ?_⟩
  have hF := (tendsto_sieveAsymptoticUpperFactor B).eventually
    (Iic_mem_nhds (show E < E + d by linarith))
  filter_upwards [eventually_sieveDensityProduct_upper B d hd, hF,
    eventually_gt_atTop (1 : ℝ)] with x hV hFx hx N hN hN2
  have hS : 0 ≤ SingularSeries.liuSingularSeries N :=
    (SingularSeries.liuSingularSeries_pos N).le
  have hlog : 0 < Real.log x := Real.log_pos hx
  calc
    sieveDensityProduct N (sieveAsymptoticZ B x) *
        (jurkatRichertUpperLinearSieveFactor (sieveAsymptoticRatio B x) + d) ≤
      sieveDensityProduct N (sieveAsymptoticZ B x) * (E + 2 * d) :=
        mul_le_mul_of_nonneg_left (by linarith) (sieveDensityProduct_nonneg N _)
    _ ≤ ((A + d) * SingularSeries.liuSingularSeries N / Real.log x) *
        (E + 2 * d) :=
      mul_le_mul_of_nonneg_right (hV N hN hN2) (by positivity)
    _ = ((A + d) * (E + 2 * d)) * SingularSeries.liuSingularSeries N /
        Real.log x := by ring
    _ ≤ (8 + ε) * SingularSeries.liuSingularSeries N / Real.log x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfinal hS) hlog.le

/-- Literal-cutoff version with an explicit real threshold, uniform in all even
`N ≥ 2` without any relation between `N` and the real scale `x`. -/
theorem exists_sieveDensityProduct_upperFactor (B ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ N : ℕ, Even N → 2 ≤ N →
        (∏ p ∈ siftingPrimes N (Real.sqrt (Real.sqrt x / Real.log x ^ B)),
          (1 - 1 / ((p : ℝ) - 1))) *
          (jurkatRichertUpperLinearSieveFactor
            (Real.log ((Real.sqrt x / Real.log x ^ B) / 2) /
              Real.log (Real.sqrt (Real.sqrt x / Real.log x ^ B))) + ρ) ≤
            (8 + ε) * SingularSeries.liuSingularSeries N / Real.log x := by
  obtain ⟨ρ, hρ, hbound⟩ := exists_eventually_sieveDensityProduct_upperFactor ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hbound B)
  refine ⟨ρ, hρ, max 2 T, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro x hx N hN hN2
  exact hT x ((le_max_right _ _).trans hx) N hN hN2

end
end Wu2004MeanValue
