import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCompletion
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Harcos's polynomial character

The coefficient formula in Harcos, §3, Definition 4 and Lemma 6
(`pages/harcos-lpolynomial-05.png`). `nextCoeff` is zero on constants;
this includes the degree-zero endpoint in the multiplicativity statement.
-/

noncomputable section

open Finset Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {p : ℕ} [Fact p.Prime]

/-- The actual polynomial character, with zero at polynomials divisible by `X`. -/
def harcosEta (a b : ZMod p) (f : (ZMod p)[X]) : ℂ :=
  if f.coeff 0 = 0 then 0 else
    ZMod.stdAddChar (-a * (f.nextCoeff / f.leadingCoeff) -
      b * (f.coeff 1 / f.coeff 0))

theorem harcosEta_zero (a b : ZMod p) : harcosEta a b 0 = 0 := by
  simp [harcosEta]

theorem harcosEta_C (a b c : ZMod p) :
    harcosEta a b (C c) = if c = 0 then 0 else 1 := by
  simp [harcosEta, nextCoeff_C_eq_zero]

theorem harcosEta_one (a b : ZMod p) : harcosEta a b 1 = 1 := by
  simpa using harcosEta_C a b 1

theorem harcosEta_norm_le_one (a b : ZMod p) (f : (ZMod p)[X]) :
    ‖harcosEta a b f‖ ≤ 1 := by
  unfold harcosEta
  split_ifs
  · simp
  · exact (stdAddChar_norm _).le

private theorem nextCoeff_div_leadingCoeff_mul (f g : (ZMod p)[X])
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).nextCoeff / (f * g).leadingCoeff =
      f.nextCoeff / f.leadingCoeff + g.nextCoeff / g.leadingCoeff := by
  have h := (monic_mul_leadingCoeff_inv hf).nextCoeff_mul
    (monic_mul_leadingCoeff_inv hg)
  rw [show (f * C f.leadingCoeff⁻¹) * (g * C g.leadingCoeff⁻¹) =
      (f * g) * C (f.leadingCoeff⁻¹ * g.leadingCoeff⁻¹) by
        rw [map_mul]; ring] at h
  simpa only [nextCoeff_mul_C, leadingCoeff_mul, mul_inv_rev, div_eq_mul_inv,
    mul_comm g.leadingCoeff⁻¹ f.leadingCoeff⁻¹] using h

theorem harcosEta_mul (a b : ZMod p) (f g : (ZMod p)[X]) :
    harcosEta a b (f * g) = harcosEta a b f * harcosEta a b g := by
  by_cases hf : f.coeff 0 = 0
  · simp [harcosEta, mul_coeff_zero, hf]
  by_cases hg : g.coeff 0 = 0
  · simp [harcosEta, mul_coeff_zero, hg]
  have hf' : f ≠ 0 := by intro h; apply hf; simp [h]
  have hg' : g ≠ 0 := by intro h; apply hg; simp [h]
  have hc : (f * g).coeff 1 / (f * g).coeff 0 =
      f.coeff 1 / f.coeff 0 + g.coeff 1 / g.coeff 0 := by
    rw [mul_coeff_one, mul_coeff_zero]
    field_simp
    ring
  rw [mul_coeff_zero] at hc
  simp only [harcosEta, mul_coeff_zero, mul_ne_zero hf hg, hf, hg, if_false]
  rw [nextCoeff_div_leadingCoeff_mul f g hf' hg', hc,
    ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The multiplicative source object for a later Euler-product construction. -/
def harcosEtaHom (a b : ZMod p) : (ZMod p)[X] →*₀ ℂ where
  toFun := harcosEta a b
  map_zero' := harcosEta_zero a b
  map_one' := harcosEta_one a b
  map_mul' := harcosEta_mul a b

theorem harcosEta_X_add_C (a b c : ZMod p) :
    harcosEta a b (X + C c) =
      if c = 0 then 0 else ZMod.stdAddChar (-a * c - b * c⁻¹) := by
  simp [harcosEta, nextCoeff_X_add_C]

theorem harcosEta_X_sub_C (a b t : ZMod p) :
    harcosEta a b (X - C t) =
      if t = 0 then 0 else ZMod.stdAddChar (a * t + b * t⁻¹) := by
  simpa [sub_eq_add_neg] using harcosEta_X_add_C a b (-t)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
