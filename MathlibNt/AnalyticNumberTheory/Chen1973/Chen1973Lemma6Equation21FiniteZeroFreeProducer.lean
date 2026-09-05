import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticConditionalCrossZeroRectangle
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Set Filter
open scoped Topology
namespace AnalyticNumberTheory.LargeSieve.Eq21FiniteZeroFreeProducer

lemma log_scales {u : ℝ} {q : ℕ} (hu : 2 ≤ u) (hq : 1 < q)
    (hqu : (q : ℝ) ≤ u ^ (100 : ℕ)) :
    1 ≤ dirichletLQuadraticConditionalCentralH q (u^2+1) ∧
    dirichletLQuadraticConditionalCentralH q (u^2+1) ≤ 105 * (1 + Real.log u) ∧
    Real.log (2 * (u^2+1) + 2) ≤ 4 * Real.log u := by
  have hu0 : 0 < u := by linarith
  have hu2 : 4 ≤ u^2 := by nlinarith
  have hu4 : u^2 + 2 ≤ u^4 := by nlinarith [sq_nonneg (u^2-2)]
  have hu4' : 2 * (u^2+1) + 2 ≤ u^4 := by nlinarith [sq_nonneg (u^2-2)]
  have hfloor : (⌊u^2+1⌋₊ : ℝ) ≤ u^2+1 := Nat.floor_le (by positivity)
  have hcut1 : 1 ≤ dirichletLNonquadraticConductorLogCutoff q (u^2+1) := by
    unfold dirichletLNonquadraticConductorLogCutoff dirichletLNonquadraticConductorLogHeightBlock
    nlinarith
  have hcutR : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q (u^2+1) := by exact_mod_cast hcut1
  have hcut : (dirichletLNonquadraticConductorLogCutoff q (u^2+1) : ℝ) ≤ u^104 := by
    unfold dirichletLNonquadraticConductorLogCutoff dirichletLNonquadraticConductorLogHeightBlock
    push_cast
    calc
      (q : ℝ) * ((⌊u^2+1⌋₊ : ℝ)+1) ≤ u^100 * u^4 := by gcongr; linarith
      _ = u^104 := by ring
  have hl := Real.log_le_log (by linarith : (0 : ℝ) < dirichletLNonquadraticConductorLogCutoff q (u^2+1)) hcut
  rw [Real.log_pow] at hl
  have hlog := Real.log_nonneg (show 1 ≤ u by linarith)
  have hl' := Real.log_le_log (by positivity : 0 < 2 * (u^2+1) + 2) hu4'
  rw [Real.log_pow] at hl'
  refine ⟨?_, ?_, by norm_num at hl'; exact hl'⟩
  · unfold dirichletLQuadraticConditionalCentralH
    linarith [Real.log_nonneg hcutR]
  · unfold dirichletLQuadraticConditionalCentralH
    norm_num at hl
    linarith

lemma log_power_absorb (C : ℝ) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ u : ℝ in atTop, C * (1 + Real.log u)^n ≤ u^r := by
  have hlo := (isLittleO_pow_exp_pos_mul_atTop n hr).comp_tendsto Real.tendsto_log_atTop
  have heps : 0 < (1 / (|C| * 2^n + 1) : ℝ) := by positivity
  filter_upwards [hlo.bound heps, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (0 : ℝ)] with u hb ht hu
  have ht0 : 0 ≤ Real.log u := by linarith
  have hp : (Real.log u)^n ≤ (1 / (|C| * 2^n + 1)) * Real.exp (r * Real.log u) := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht0 n),
      abs_of_pos (Real.exp_pos _)] using hb
  have hs : (1 + Real.log u)^n ≤ (2 * Real.log u)^n := by gcongr; linarith
  calc
    _ ≤ |C| * (1 + Real.log u)^n := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 * Real.log u)^n := mul_le_mul_of_nonneg_left hs (abs_nonneg C)
    _ = (|C| * 2^n) * (Real.log u)^n := by rw [mul_pow]; ring
    _ ≤ (|C| * 2^n) * ((1 / (|C| * 2^n + 1)) * Real.exp (r * Real.log u)) := by gcongr
    _ ≤ Real.exp (r * Real.log u) := by
      have hc : (|C| * 2^n) / (|C| * 2^n+1) ≤ (1 : ℝ) := by
        apply (div_le_one (by positivity)).mpr; linarith
      calc
        _ = ((|C| * 2^n) / (|C| * 2^n+1)) * Real.exp (r * Real.log u) := by ring
        _ ≤ 1 * Real.exp (r * Real.log u) := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
        _ = _ := one_mul _
    _ = u^r := by rw [Real.rpow_def_of_pos hu]; congr 1; ring

lemma fixedH_bound {u c η : ℝ} {q : ℕ} (hu : 2 ≤ u) (hc : 0 < c)
    (hη : 0 ≤ η) (hq : 1 < q) (hqu : (q : ℝ) ≤ u^(100 : ℕ)) :
    0 < dirichletLQuadraticConditionalFixedH q
      (dirichletLQuadraticConditionalCentralHeight c η q (u^2+1)) (u^2+1) ∧
    dirichletLQuadraticConditionalFixedH q
      (dirichletLQuadraticConditionalCentralHeight c η q (u^2+1)) (u^2+1)
      ≤ (1000 + 3000000 / c) * (q : ℝ)^η * (1 + Real.log u)^2 := by
  obtain ⟨hH1, hHle, hlog⟩ := log_scales hu hq hqu
  let H := dirichletLQuadraticConditionalCentralH q (u^2+1)
  let L := 1 + Real.log u
  let Q := (q : ℝ)^η
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hq0 _
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hq1 hη
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (show 1 ≤ u by linarith)]
  have hL0 : 0 ≤ L := by linarith
  have hH0 : 0 < H := by dsimp [H]; linarith
  have hH : H ≤ 105 * L := hHle
  have hHsq : H^2 ≤ 105^2 * L^2 := by nlinarith [sq_le_sq₀ hH0.le (by positivity) |>.mpr hH]
  have hneg : (q : ℝ)^(-η) = Q⁻¹ := Real.rpow_neg hq0.le η
  have hb : 0 < c * (q : ℝ)^(-η) / (256 * H^2) := by positivity
  have ht : 0 < dirichletLQuadraticConditionalCentralHeight c η q (u^2+1) := by
    unfold dirichletLQuadraticConditionalCentralHeight
    exact lt_min (by positivity) hb
  have hinv : 1 / (2 * dirichletLQuadraticConditionalCentralHeight c η q (u^2+1))
      ≤ 1 + (128 / c) * H^2 * Q := by
    unfold dirichletLQuadraticConditionalCentralHeight
    change 1 / (2 * min (u^2+1) (c * (q : ℝ)^(-η) / (256*H^2))) ≤ _
    by_cases hm : u^2+1 ≤ c * (q : ℝ)^(-η) / (256*H^2)
    · rw [min_eq_left hm]
      have hi : 1 / (2 * (u^2+1)) ≤ (1 : ℝ) := by
        apply (div_le_one (by positivity)).mpr; nlinarith [sq_nonneg u]
      have hn : 0 ≤ (128 / c) * H^2 * Q := by positivity
      linarith
    · rw [min_eq_right (le_of_not_ge hm), hneg]
      have he : 1 / (2 * (c * Q⁻¹ / (256*H^2))) = (128/c)*H^2*Q := by
        field_simp; ring
      rw [he]; linarith
  have hlog0 : 0 ≤ Real.log (2 * (u^2+1)+2) := Real.log_nonneg (by nlinarith [sq_nonneg u])
  have hLsq : L ≤ L^2 := by nlinarith
  have hQL : L^2 ≤ Q * L^2 := by nlinarith [sq_nonneg L]
  have hbase : H + 1 + Real.log (2 * (u^2+1)+2) + 1 ≤ 110 * L := by
    dsimp [L] at *; linarith
  have hlarge : (128 / c) * H^2 * Q ≤ (3000000/c) * Q * L^2 := by
    calc
      _ ≤ (128/c) * (105^2 * L^2) * Q := by gcongr
      _ ≤ (3000000/c) * Q * L^2 := by
        have hc' : 128 * (105 : ℝ)^2 / c ≤ 3000000 / c := by gcongr; norm_num
        calc
          _ = (128 * (105 : ℝ)^2 / c) * (Q * L^2) := by ring
          _ ≤ (3000000/c) * (Q * L^2) := mul_le_mul_of_nonneg_right hc' (by positivity)
          _ = _ := by ring
  change 0 < H + (1 + Real.log (2*(u^2+1)+2) +
      1 / (2 * dirichletLQuadraticConditionalCentralHeight c η q (u^2+1))) ∧ _
  constructor
  · positivity
  · change H + (1 + Real.log (2*(u^2+1)+2) +
      1 / (2 * dirichletLQuadraticConditionalCentralHeight c η q (u^2+1))) ≤ _
    change _ ≤ (1000 + 3000000/c) * Q * L^2
    nlinarith

lemma nonquadratic_width_eventually :
    ∀ᶠ u : ℝ in atTop, ∀ q : ℕ, 1 < q → (q : ℝ) ≤ u^(100 : ℕ) →
      2 / Real.sqrt u ≤ 1 / (274877906944 *
        (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q (u^2+1)))^9) := by
  filter_upwards [log_power_absorb (2 * 274877906944 * 105^9) 9
    (by norm_num : (0 : ℝ) < 1/2), eventually_ge_atTop (2 : ℝ)] with u hab hu
  intro q hq hqu
  obtain ⟨hH1, hHle, _⟩ := log_scales hu hq hqu
  let H := dirichletLQuadraticConditionalCentralH q (u^2+1)
  have hH0 : 0 < H := by dsimp [H]; linarith
  have hL0 : 0 ≤ 1 + Real.log u := by linarith [Real.log_nonneg (show 1 ≤ u by linarith)]
  have hpow : H^9 ≤ 105^9 * (1 + Real.log u)^9 := by
    calc
      _ ≤ (105 * (1 + Real.log u))^9 := pow_le_pow_left₀ hH0.le hHle 9
      _ = _ := mul_pow _ _ _
  have hpay : 2 * (274877906944 * H^9) ≤ Real.sqrt u := by
    rw [Real.sqrt_eq_rpow]
    nlinarith
  change 2 / Real.sqrt u ≤ 1 / (274877906944 * H^9)
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 (by linarith)) (by positivity)]
  simpa using hpay

lemma quadratic_denominator_bound {u c η : ℝ} {q : ℕ} (hu : 2 ≤ u) (hc : 0 < c)
    (hη : 0 ≤ η) (hq : 1 < q) (hqu : (q : ℝ) ≤ u^(100 : ℕ)) :
    (q : ℝ)^(2*η) * (dirichletLQuadraticConditionalFixedH q
      (dirichletLQuadraticConditionalCentralHeight c η q (u^2+1)) (u^2+1))^12
    ≤ (1000+3000000/c)^12 * (q : ℝ)^(14*η) * (1 + Real.log u)^24 := by
  obtain ⟨hH0, hH⟩ := fixedH_bound hu hc hη hq hqu
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hp := pow_le_pow_left₀ hH0.le hH 12
  calc
    _ ≤ (q : ℝ)^(2*η) * ((1000+3000000/c) * (q : ℝ)^η * (1+Real.log u)^2)^12 := by gcongr
    _ = (1000+3000000/c)^12 * ((q : ℝ)^(2*η) * ((q : ℝ)^η)^12) * (1+Real.log u)^24 := by ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hq0.le, ← Real.rpow_add hq0]
      norm_num only [Nat.cast_ofNat]
      rw [show 2*η + η*(12 : ℝ) = 14*η by ring]

lemma quadratic_width_eventually_real (c A : ℝ) (hc : 0 < c) (hA : 0 < A) :
    ∀ᶠ u : ℝ in atTop, ∀ q : ℕ, 1 < q → (q : ℝ) ≤ u^(100 : ℕ) →
      2 / Real.sqrt u ≤ dirichletLQuadraticConditionalCrossZeroWidth
        A c (1/10000) q (u^2+1) := by
  let C := 1000 + 3000000/c
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [log_power_absorb (2*C^12/A) 24 (by norm_num : (0 : ℝ) < 9/25),
    eventually_ge_atTop (2 : ℝ)] with u hab hu
  intro q hq hqu
  have hu0 : 0 < u := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  let H := dirichletLQuadraticConditionalFixedH q
    (dirichletLQuadraticConditionalCentralHeight c (1/10000) q (u^2+1)) (u^2+1)
  have hH0 : 0 < H := (fixedH_bound hu hc (by norm_num : (0 : ℝ) ≤ 1/10000) hq hqu).1
  have hden := quadratic_denominator_bound hu hc (by norm_num : (0 : ℝ) ≤ 1/10000) hq hqu
  have hqp : (q : ℝ)^(14*(1/10000 : ℝ)) ≤ u^(7/50 : ℝ) := by
    calc
      _ ≤ (u^(100 : ℕ))^(14*(1/10000 : ℝ)) := Real.rpow_le_rpow hq0.le hqu (by norm_num)
      _ = _ := by rw [← Real.rpow_natCast_mul hu0.le]; norm_num
  have hden' : (q : ℝ)^(2*(1/10000 : ℝ)) * H^12 ≤ C^12 * u^(7/50 : ℝ) * (1+Real.log u)^24 := by
    calc
      _ ≤ C^12 * (q : ℝ)^(14*(1/10000 : ℝ)) * (1+Real.log u)^24 := hden
      _ ≤ _ := by gcongr
  have hab' : 2*C^12 * (1+Real.log u)^24 ≤ A * u^(9/25 : ℝ) := by
    rw [mul_comm A]
    apply (div_le_iff₀ hA).mp
    simpa only [div_mul_eq_mul_div] using hab
  have hpay : 2 * ((q : ℝ)^(2*(1/10000 : ℝ)) * H^12) ≤ A * Real.sqrt u := by
    calc
      _ ≤ 2 * (C^12 * u^(7/50 : ℝ) * (1+Real.log u)^24) := by gcongr
      _ = u^(7/50 : ℝ) * (2*C^12 * (1+Real.log u)^24) := by ring
      _ ≤ u^(7/50 : ℝ) * (A * u^(9/25 : ℝ)) := by gcongr
      _ = A * Real.sqrt u := by
        rw [Real.sqrt_eq_rpow]
        calc
          _ = A * (u^(7/50 : ℝ) * u^(9/25 : ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add hu0]; norm_num
  have he : dirichletLQuadraticConditionalCrossZeroWidth A c (1/10000) q (u^2+1) =
      A / ((q : ℝ)^(2*(1/10000 : ℝ)) * H^12) := by
    unfold dirichletLQuadraticConditionalCrossZeroWidth
    change A * (q : ℝ)^(-2*(1/10000 : ℝ)) / H^12 = _
    rw [show (-2*(1/10000 : ℝ)) = -(2*(1/10000 : ℝ)) by ring, Real.rpow_neg hq0.le]
    field_simp
  rw [he, div_le_div_iff₀ (Real.sqrt_pos.2 hu0) (by positivity)]
  exact hpay

/-- The threshold precedes the modulus, and η is fixed once and for all. -/
theorem quadraticCrossZeroWidth_eventually (c A : ℝ) (hc : 0 < c) (hA : 0 < A) :
    ∃ X₀ : ℕ, ∀ x ≥ X₀, ∀ q : ℕ, 1 < q → (q : ℝ) ≤ Real.log (x : ℝ)^(100 : ℕ) →
      2 / Real.sqrt (Real.log (x : ℝ)) ≤ dirichletLQuadraticConditionalCrossZeroWidth
        A c (1/10000) q ((Real.log (x : ℝ))^2+1) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (hlog.eventually (quadratic_width_eventually_real c A hc hA))

lemma rectangle_mem {a T : ℝ} {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ 2)
    (ht : |s.im| ≤ T) :
    s ∈ ((a : ℂ) - Complex.I * T).Rectangle (2 + Complex.I * T) := by
  rw [Complex.Rectangle, Complex.mem_reProdIm]
  norm_num
  exact ⟨Set.Icc_subset_uIcc ⟨ha, hb⟩, Set.Icc_subset_uIcc (abs_le.mp ht)⟩

lemma nonquadratic_rectangle_eventually_real :
    ∀ᶠ u : ℝ in atTop, ∀ (q : ℕ) (hq : 1 < q),
      let : NeZero q := ⟨by omega⟩
      (q : ℝ) ≤ u^(100 : ℕ) →
      ∀ χ : DirichletCharacter ℂ q, χ^2 ≠ 1 → ∀ s : ℂ,
      1 - 2 / Real.sqrt u ≤ s.re → s.re ≤ 2 → |s.im| ≤ u^2+1 →
      χ.LFunction s ≠ 0 := by
  filter_upwards [nonquadratic_width_eventually, eventually_ge_atTop (2 : ℝ)] with u hw hu
  intro q hq
  dsimp only
  let : NeZero q := ⟨by omega⟩
  intro hqu χ hχ s hs hs2 ht
  have hw' := hw q hq hqu
  apply LFunction_ne_zero_on_nonquadratic_conductorLogRectangle χ hχ (by nlinarith : 3 ≤ u^2+1) s
  apply rectangle_mem (hb := hs2) (ht := ht)
  unfold dirichletLNonquadraticConductorLogLeftEdge
  linarith

/-- No Siegel premise is needed in the nonquadratic branch. -/
theorem nonquadratic_rectangle_eventually :
    ∃ X₀ : ℕ, ∀ x ≥ X₀, ∀ (q : ℕ) (hq : 1 < q),
      let : NeZero q := ⟨by omega⟩
      (q : ℝ) ≤ Real.log (x : ℝ)^(100 : ℕ) →
      ∀ χ : DirichletCharacter ℂ q, χ^2 ≠ 1 → ∀ s : ℂ,
      1 - 2 / Real.sqrt (Real.log (x : ℝ)) ≤ s.re → s.re ≤ 2 →
      |s.im| ≤ (Real.log (x : ℝ))^2+1 → χ.LFunction s ≠ 0 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (hlog.eventually nonquadratic_rectangle_eventually_real)

/-- Finite Eq21 nonvanishing, conditional only on the displayed raw quadratic
`L(1)` lower bound with one fixed c and η=1/10000. The threshold is chosen
before x, q, the character and every rectangle point. No all-height assertion
and no assertion that the Siegel lower bound has been proved is made. -/
theorem finiteRectangle_of_fixedSiegel (c : ℝ) (hc : 0 < c) :
    ∃ X₀ : ℕ, ∀ x ≥ X₀, ∀ (q : ℕ) (hq : 1 < q),
      let : NeZero q := ⟨by omega⟩
      (q : ℝ) ≤ Real.log (x : ℝ)^(100 : ℕ) →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      (χ^2 = 1 → c * (q : ℝ)^(-(1/10000 : ℝ)) ≤ (χ.LFunction 1).re) →
      ∀ s : ℂ, 1 - 2 / Real.sqrt (Real.log (x : ℝ)) ≤ s.re → s.re ≤ 2 →
      |s.im| ≤ (Real.log (x : ℝ))^2+1 → χ.LFunction s ≠ 0 := by
  obtain ⟨A, hA, hzero⟩ := exists_LFunction_ne_zero_on_quadraticConditionalCrossZeroRectangle
    c (1/10000) hc (by norm_num)
  obtain ⟨X₁, hwidth⟩ := quadraticCrossZeroWidth_eventually c A hc hA
  obtain ⟨X₂, hnonquad⟩ := nonquadratic_rectangle_eventually
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx q hq
  dsimp only
  let : NeZero q := ⟨by omega⟩
  intro hqu χ hprim hSiegel s hs hs2 ht
  by_cases hquad : χ^2 = 1
  · have hχ : χ ≠ 1 := by
      intro he
      rw [DirichletCharacter.IsPrimitive, he, DirichletCharacter.conductor_one] at hprim
      omega
    have hw := hwidth x ((le_max_left _ _).trans hx) q hq hqu
    apply hzero q χ ((Real.log (x : ℝ))^2+1) hquad hχ (by positivity) (hSiegel hquad) s
    apply rectangle_mem (hb := hs2) (ht := ht)
    linarith
  · exact hnonquad x ((le_max_right _ _).trans hx) q hq hqu χ hquad s hs hs2 ht

end AnalyticNumberTheory.LargeSieve.Eq21FiniteZeroFreeProducer
