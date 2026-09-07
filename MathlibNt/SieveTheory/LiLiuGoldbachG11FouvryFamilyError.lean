import MathlibNt.SieveTheory.LiLiuGoldbachG11FouvryRectangle
import MathlibNt.SieveTheory.LiLiuFouvryG9WFBridge

open Filter Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Each original external-family member is supplied internally, and the
whole finite family is paid. This is one rectangle, not the full moving-region sum. -/
theorem goldbachG11_Fouvry_externalFamily_rectangle (A : ℕ) {Cscale η θ : ℝ}
    (hCscale : 1 ≤ Cscale) (hη : 0 < η) (hθ : 0 < θ) (hθu : θ < 1/8) :
    ∀ᶠ x : ℝ in atTop, ∀ z : PrimeC2Interval, ∀ M ν : ℝ,
      1 ≤ M → 4*M*z.scale = x → η ≤ ν → ν ≤ 1/10+η/10 → z.scale = x^ν →
      ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x →
      ∀ U : Finset ℕ, (∀ m ∈ U, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2*M) →
      ∀ (P : Finset ℕ) (y : ℝ),
      2 ≤ externalInternalLevel (x^((5-5*ν)/9-η)) θ →
        (∑ t ∈ externalTags true P (externalInternalLevel (x^((5-5*ν)/9-η)) θ) θ y,
          |signedError U (primeSWInterval z.lower z.upper)
            (Ioc 0 ⌊x^((5-5*ν)/9-η)⌋₊)
            (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
              ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
            (fun p => if p.Coprime N then primeSWBeta p else 0)
            (fun d => externalTerm true P (externalInternalLevel (x^((5-5*ν)/9-η)) θ) θ y t d)
            (N : ℤ)|) ≤ x/Real.log x^A := by
  let B : ℝ := Real.exp (8*(θ⁻¹)^3)
  have hB : 0 < B := Real.exp_pos _
  filter_upwards [goldbachG11_Fouvry_rectangle 1 (A+1) hCscale hη,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop B),
    eventually_ge_atTop (0 : ℝ)] with x hx hlog hx0
  intro z M ν hM hMT hην hν hT N hN hNx U hU P y hD
  let Q : ℝ := x^((5-5*ν)/9-η)
  let D : ℝ := externalInternalLevel Q θ
  have hQ : 0 ≤ Q := Real.rpow_nonneg hx0 _
  have hcard : ((externalTags true P D θ y).card : ℝ) ≤ B :=
    (externalTags_card_and_wellFactorable true P y hD hθ hθu).1.le
  have heach : ∀ t ∈ externalTags true P D θ y,
      |signedError U (primeSWInterval z.lower z.upper) (Ioc 0 ⌊Q⌋₊)
        (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
          ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
        (fun p => if p.Coprime N then primeSWBeta p else 0)
        (fun d => externalTerm true P D θ y t d) (N : ℤ)| ≤
        x/Real.log x^(A+1) := by
    intro t ht
    exact hx z M ν hM hMT hην hν hT N hN hNx U hU _
      (externalTerm_signedWellFactorable true P y t hQ hD hθ hθu ht)
  have hs := sum_le_sum heach
  simp only [sum_const, nsmul_eq_mul] at hs
  have hp : 0 < Real.log x := hB.trans_le hlog
  have hpay : B*(x/Real.log x^(A+1)) ≤ x/Real.log x^A := by
    rw [pow_succ]
    apply (le_div_iff₀ (pow_pos hp A)).2
    have he : B*(x/(Real.log x^A*Real.log x))*Real.log x^A = B*x/Real.log x := by
      field_simp
    rw [he]
    exact (div_le_iff₀ hp).2 (by nlinarith)
  exact hs.trans ((mul_le_mul_of_nonneg_right hcard (by positivity)).trans hpay)

/-- Uniform growth of the unchanged internal level, before all moving short exponents. -/
theorem goldbachG11_Fouvry_internalLevel_eventually (D₀ : ℝ) (hD₀ : 0 ≤ D₀)
    {η θ : ℝ} (hηu : η < 1/8) (hθ : 0 < θ) (hθu : θ < 1/8) :
    ∀ᶠ x : ℝ in atTop, ∀ ν : ℝ, ν ≤ 1/10+η/10 →
      D₀ ≤ externalInternalLevel (x^((5-5*ν)/9-η)) θ := by
  have hg := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).eventually
    (eventually_ge_atTop (D₀^(1+θ+θ^9)))
  filter_upwards [hg, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro ν hν
  apply externalInternalLevel_ge_threshold hD₀ hθ hθu
  exact hx.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))

/-- Fully supplied external-family discrepancy on one actual G11 rectangle.
No coefficient, SW, WF-member, cardinality or internal-level premise remains. -/
theorem goldbachG11_Fouvry_externalFamily_rectangle_paid (A : ℕ) {Cscale η θ : ℝ}
    (hCscale : 1 ≤ Cscale) (hη : 0 < η) (hηu : η < 1/8) (hθ : 0 < θ) (hθu : θ < 1/8) :
    ∀ᶠ x : ℝ in atTop, ∀ z : PrimeC2Interval, ∀ M ν : ℝ,
      1 ≤ M → 4*M*z.scale = x → η ≤ ν → ν ≤ 1/10+η/10 → z.scale = x^ν →
      ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x →
      ∀ U : Finset ℕ, (∀ m ∈ U, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2*M) →
      ∀ (P : Finset ℕ) (y : ℝ),
        (∑ t ∈ externalTags true P (externalInternalLevel (x^((5-5*ν)/9-η)) θ) θ y,
          |signedError U (primeSWInterval z.lower z.upper)
            (Ioc 0 ⌊x^((5-5*ν)/9-η)⌋₊)
            (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
              ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
            (fun p => if p.Coprime N then primeSWBeta p else 0)
            (fun d => externalTerm true P (externalInternalLevel (x^((5-5*ν)/9-η)) θ) θ y t d)
            (N : ℤ)|) ≤ x/Real.log x^A := by
  filter_upwards [goldbachG11_Fouvry_externalFamily_rectangle A hCscale hη hθ hθu,
    goldbachG11_Fouvry_internalLevel_eventually 2 (by norm_num) hηu hθ hθu]
    with x hx hgate
  intro z M ν hM hMT hην hν hT N hN hNx U hU P y
  exact hx z M ν hM hMT hην hν hT N hN hNx U hU P y (hgate ν hν)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig