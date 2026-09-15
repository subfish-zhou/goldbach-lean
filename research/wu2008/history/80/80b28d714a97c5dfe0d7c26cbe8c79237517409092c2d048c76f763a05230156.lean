import MathlibNt.Wu2008DoubleSieve.Gamma16IntegralRegular

/-!
# The literal fourth-row fourfold integral and its finite phi envelope

The integration order is w,t,u,v on a <= t <= u <= v <= w <= b.
No factorial or pointwise supremum is inserted.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory LiLiuPrereqBuchstab
open scoped Interval

def gamma16ExponentRegion : Set (ℝ × ℝ × ℝ × ℝ) :=
  {p | gamma16Alpha ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2.1 ∧
    p.2.2.1 ≤ p.2.2.2 ∧ p.2.2.2 ≤ gamma16Beta}

theorem gamma16_exponent_region_fibres (t u v w : ℝ) :
    (t, u, v, w) ∈ gamma16ExponentRegion ↔
      w ∈ Icc gamma16Alpha gamma16Beta ∧ t ∈ Icc gamma16Alpha w ∧
        u ∈ Icc t w ∧ v ∈ Icc u w := by
  constructor
  · rintro ⟨hat, htu, huv, hvw, hwb⟩
    exact ⟨⟨hat.trans (htu.trans (huv.trans hvw)), hwb⟩,
      ⟨hat, htu.trans (huv.trans hvw)⟩, ⟨htu, huv.trans hvw⟩, ⟨huv, hvw⟩⟩
  · rintro ⟨hw, ht, hu, hv⟩
    exact ⟨ht.1, hu.1, hv.1, hv.2, hw.2⟩

noncomputable def gamma16FourthIntegral (φ : ℝ) : ℝ :=
  ∫ w in gamma16Alpha..gamma16Beta, ∫ t in gamma16Alpha..w,
    ∫ u in t..w, ∫ v in u..w,
      buchstab ((φ - t - u - v - w) / v) / (t * u * v ^ 2 * w)

theorem gamma16_fourth_integral_eq_outer (φ : ℝ) :
    gamma16FourthIntegral φ =
      ∫ w in gamma16Alpha..gamma16Beta, gamma16OuterWeight φ w / w := by
  unfold gamma16FourthIntegral
  symm
  apply intervalIntegral.integral_congr
  intro w hw
  rw [uIcc_of_le gamma16_constants.2.1] at hw
  change primeOrderedTripleIntegral gamma16Alpha w (gamma16ClippedKernel φ w) / w = _
  rw [primeOrderedTripleIntegral_eq, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hw.1] at ht
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht.2] at hu
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hu.2] at hv
  dsimp only
  have ht' : t ∈ Icc gamma16Alpha gamma16Beta := ⟨ht.1, ht.2.trans hw.2⟩
  have hu' : u ∈ Icc gamma16Alpha gamma16Beta := ⟨ht.1.trans hu.1, hu.2.trans hw.2⟩
  have hv' : v ∈ Icc gamma16Alpha gamma16Beta :=
    ⟨(ht.1.trans hu.1).trans hv.1, hv.2.trans hw.2⟩
  rw [gamma16ClippedKernel, gamma16_clip_eq ht', gamma16_clip_eq hu',
    gamma16_clip_eq hv', gamma16_clip_eq hw, gamma16Kernel]
  ring

theorem gamma16_fourth_integral_nonneg {φ : ℝ} (hφ : 2 ≤ φ) :
    0 ≤ gamma16FourthIntegral φ := by
  unfold gamma16FourthIntegral
  apply intervalIntegral.integral_nonneg gamma16_constants.2.1
  intro w hw
  apply intervalIntegral.integral_nonneg hw.1
  intro t ht
  apply intervalIntegral.integral_nonneg ht.2
  intro u hu
  apply intervalIntegral.integral_nonneg hu.2
  intro v hv
  have ht' : t ∈ Icc gamma16Alpha gamma16Beta := ⟨ht.1, ht.2.trans hw.2⟩
  have hu' : u ∈ Icc gamma16Alpha gamma16Beta := ⟨ht.1.trans hu.1, hu.2.trans hw.2⟩
  have hv' : v ∈ Icc gamma16Alpha gamma16Beta :=
    ⟨(ht.1.trans hu.1).trans hv.1, hv.2.trans hw.2⟩
  exact div_nonneg (buchstab_nonneg (gamma16_argument_one hφ ht' hu' hv' hw))
    (mul_nonneg (mul_nonneg (mul_nonneg
      (by linarith [gamma16_constants.1, ht'.1])
      (by linarith [gamma16_constants.1, hu'.1])) (sq_nonneg v))
      (by linarith [gamma16_constants.1, hw.1]))

theorem gamma16_fourth_integral_bound {φ : ℝ} (hφ : 2 ≤ φ) :
    gamma16FourthIntegral φ ≤ 2560 := by
  rw [gamma16_fourth_integral_eq_outer]
  have h := primeOrdered_integral_norm_le_four
    ⟨gamma16_constants.1, gamma16_constants.2.1.trans gamma16_constants.2.2.1⟩
    ⟨gamma16_constants.1.trans gamma16_constants.2.1, gamma16_constants.2.2.1⟩
    (by norm_num : (0 : ℝ) ≤ 640) (gamma16_outer_regular hφ (le_refl φ)).1
  exact (le_abs_self _).trans (by simpa only [show (4 : ℝ) * 640 = 2560 by norm_num] using h)

theorem gamma16_fourth_image_nonempty :
    ((fun φ => gamma16FourthIntegral φ) '' Ici 2).Nonempty :=
  ⟨gamma16FourthIntegral 2, mem_image_of_mem _ (by norm_num)⟩

theorem gamma16_fourth_image_bddAbove :
    BddAbove ((fun φ => gamma16FourthIntegral φ) '' Ici 2) := by
  refine ⟨2560, ?_⟩
  rintro y ⟨φ, hφ, rfl⟩
  exact gamma16_fourth_integral_bound hφ

noncomputable def gamma16FourthIntegralEnvelope : ℝ :=
  sSup ((fun φ => gamma16FourthIntegral φ) '' Ici 2)

theorem gamma16_fourth_le_envelope {φ : ℝ} (hφ : 2 ≤ φ) :
    gamma16FourthIntegral φ ≤ gamma16FourthIntegralEnvelope :=
  le_csSup gamma16_fourth_image_bddAbove (mem_image_of_mem _ hφ)

theorem gamma16_fourth_envelope_bounds :
    0 ≤ gamma16FourthIntegralEnvelope ∧ gamma16FourthIntegralEnvelope ≤ 2560 :=
  ⟨(gamma16_fourth_integral_nonneg (le_refl 2)).trans (gamma16_fourth_le_envelope (le_refl 2)),
    csSup_le gamma16_fourth_image_nonempty (by
      rintro y ⟨φ, hφ, rfl⟩
      exact gamma16_fourth_integral_bound hφ)⟩

end Wu2008DoubleSieve
