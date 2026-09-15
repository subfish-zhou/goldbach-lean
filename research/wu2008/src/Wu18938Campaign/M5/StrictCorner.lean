import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

namespace Wu18938Campaign.M5.StrictCorner

open Real Set MeasureTheory Filter
open scoped Classical Topology

def rectangle (a b c d : ℝ) : Set (ℝ × ℝ) := Ico a b ×ˢ Ico c d

def mass (f : ℝ × ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  ∫ z in rectangle a b c d, f z

theorem rectangle_measurable (a b c d : ℝ) :
    MeasurableSet (rectangle a b c d) :=
  measurableSet_Ico.prod measurableSet_Ico

theorem rectangle_finite (a b c d : ℝ) :
    volume (rectangle a b c d) < ⊤ := by
  apply lt_of_le_of_lt (measure_mono (show rectangle a b c d ⊆ Icc a b ×ˢ Icc c d from
    fun _ h => ⟨⟨h.1.1, h.1.2.le⟩, h.2.1, h.2.2.le⟩))
  exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top

theorem rectangle_integrable {f : ℝ × ℝ → ℝ} {a b c d K : ℝ}
    (hf : Measurable f) (hb : ∀ z ∈ rectangle a b c d, ‖f z‖ ≤ K) :
    IntegrableOn f (rectangle a b c d) := by
  apply Measure.integrableOn_of_bounded (rectangle_finite a b c d).ne
    hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (rectangle_measurable a b c d)] with z hz
  exact hb z hz

theorem mass_split {f : ℝ × ℝ → ℝ} {a b c d t : ℝ}
    (hct : c ≤ t) (htd : t ≤ d) (hf : IntegrableOn f (rectangle a b c d)) :
    mass f a b c d - mass f a b c t = mass f a b t d := by
  have hsT : rectangle a b c t ⊆ rectangle a b c d :=
    fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans_le htd⟩
  have hsS : rectangle a b t d ⊆ rectangle a b c d :=
    fun _ hz => ⟨hz.1, hct.trans hz.2.1, hz.2.2⟩
  have hiT := (hf.mono_set hsT).integrable_indicator (rectangle_measurable a b c t)
  have hiS := (hf.mono_set hsS).integrable_indicator (rectangle_measurable a b t d)
  have he : (rectangle a b c d).indicator f =
      (rectangle a b c t).indicator f + (rectangle a b t d).indicator f := by
    funext z
    by_cases hz : z ∈ rectangle a b c d
    · by_cases hzt : z.2 < t
      · have hT : z ∈ rectangle a b c t := ⟨hz.1, hz.2.1, hzt⟩
        have hS : z ∉ rectangle a b t d := fun h => (not_lt_of_ge h.2.1) hzt
        simp only [Pi.add_apply, indicator_of_mem hz, indicator_of_mem hT,
          indicator_of_notMem hS, add_zero]
      · have hS : z ∈ rectangle a b t d := ⟨hz.1, le_of_not_gt hzt, hz.2.2⟩
        have hT : z ∉ rectangle a b c t := fun h => hzt h.2.2
        simp only [Pi.add_apply, indicator_of_mem hz, indicator_of_mem hS,
          indicator_of_notMem hT, zero_add]
    · have hT : z ∉ rectangle a b c t := fun h => hz (hsT h)
      have hS : z ∉ rectangle a b t d := fun h => hz (hsS h)
      simp only [Pi.add_apply, indicator_of_notMem hz, indicator_of_notMem hT,
        indicator_of_notMem hS, zero_add]
  have hi := congrArg (fun g : ℝ × ℝ → ℝ => ∫ z, g z) he
  simp only [Pi.add_apply] at hi
  rw [integral_add hiT hiS, integral_indicator (rectangle_measurable a b c d),
    integral_indicator (rectangle_measurable a b c t),
    integral_indicator (rectangle_measurable a b t d)] at hi
  exact sub_eq_iff_eq_add.mpr (by simpa only [mass, add_comm] using hi)

theorem mass_strip_error {f : ℝ × ℝ → ℝ} {a b c d η K : ℝ}
    (hab : a ≤ b) (hη : 0 ≤ η) (hηd : c ≤ d - η)
    (hf : Measurable f) (hb : ∀ z ∈ rectangle a b c d, ‖f z‖ ≤ K) :
    |mass f a b c d - mass f a b c (d - η)| ≤ K * (b - a) * η := by
  have hs : rectangle a b (d - η) d ⊆ rectangle a b c d :=
    fun _ hz => ⟨hz.1, hηd.trans hz.2.1, hz.2.2⟩
  rw [mass_split hηd (sub_le_self _ hη) (rectangle_integrable hf hb)]
  have hn := norm_setIntegral_le_of_norm_le_const
    (f := f) (C := K) (rectangle_finite a b (d - η) d) (fun z hz => hb z (hs hz))
  have hv : volume.real (rectangle a b (d - η) d) = (b - a) * η := by
    change (volume (rectangle a b (d - η) d)).toReal = _
    rw [rectangle, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod,
      Real.volume_Ico, Real.volume_Ico, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
      ENNReal.toReal_ofReal (by linarith : 0 ≤ d - (d - η))]
    ring
  rw [hv, Real.norm_eq_abs] at hn
  simpa only [mass, mul_assoc] using hn

def originalMass (f : ℝ × ℝ → ℝ) (η : ℝ) : ℝ :=
  4 * mass f (100 / 1327) (25 / 206) (25 / 206) (1 / 2 - 2 * (25 / 206) - η) +
  4 * mass f (100 / 1327) (3 * (100 / 1327) / 2)
    (1 / 2 - 2 * (25 / 206)) (1 / 2 - 3 * (100 / 1327) - η)

def originalEnvelope : Set (ℝ × ℝ) :=
  rectangle (100 / 1327) (25 / 206) (25 / 206) (1 / 2 - 3 * (100 / 1327))

theorem original_uniform_error {f : ℝ × ℝ → ℝ} {η K : ℝ}
    (hη : 0 ≤ η) (hηhi : η ≤ 1 / 100) (hf : Measurable f)
    (hb : ∀ z ∈ originalEnvelope, ‖f z‖ ≤ K) :
    |originalMass f 0 - originalMass f η| ≤
      4 * K * ((25 / 206 : ℝ) - (100 / 1327) / 2) * η := by
  have ha := mass_strip_error (a := (100 / 1327 : ℝ)) (b := (25 / 206 : ℝ))
    (c := (25 / 206 : ℝ)) (d := 1 / 2 - 2 * (25 / 206 : ℝ))
    (η := η) (K := K) (by norm_num) hη (by linarith) hf
    (fun z hz => hb z ⟨hz.1, hz.2.1, hz.2.2.trans_le (by norm_num)⟩)
  have hb' := mass_strip_error (a := (100 / 1327 : ℝ))
    (b := 3 * (100 / 1327 : ℝ) / 2)
    (c := 1 / 2 - 2 * (25 / 206 : ℝ)) (d := 1 / 2 - 3 * (100 / 1327 : ℝ))
    (η := η) (K := K) (by norm_num) hη (by linarith) hf
    (fun z hz => hb z
      ⟨⟨hz.1.1, hz.1.2.trans_le (by norm_num)⟩,
        (by norm_num : (25 / 206 : ℝ) ≤ 1 / 2 - 2 * (25 / 206)).trans hz.2.1, hz.2.2⟩)
  unfold originalMass
  simp only [sub_zero]
  have he : ∀ a b c d : ℝ, 4 * a + 4 * b - (4 * c + 4 * d) =
      4 * ((a - c) + (b - d)) := by intros; ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have ht := abs_add_le
    (mass f (100 / 1327) (25 / 206) (25 / 206) (1 / 2 - 2 * (25 / 206)) -
      mass f (100 / 1327) (25 / 206) (25 / 206) (1 / 2 - 2 * (25 / 206) - η))
    (mass f (100 / 1327) (3 * (100 / 1327) / 2)
        (1 / 2 - 2 * (25 / 206)) (1 / 2 - 3 * (100 / 1327)) -
      mass f (100 / 1327) (3 * (100 / 1327) / 2)
        (1 / 2 - 2 * (25 / 206)) (1 / 2 - 3 * (100 / 1327) - η))
  nlinarith only [ha, hb', ht]

theorem original_strict_slack {η δ : ℝ} (hη : 0 < η) (hδ : δ ≤ η) :
    2 * (25 / 206 : ℝ) + (1 / 2 - 2 * (25 / 206) - η) < 1 / 2 ∧
      2 * (3 * (100 / 1327 : ℝ) / 2) + (1 / 2 - 3 * (100 / 1327) - η) < 1 / 2 ∧
      2 * (25 / 206 : ℝ) + (1 / 2 - 2 * (25 / 206) - η) ≤ 1 / 2 - δ ∧
      2 * (3 * (100 / 1327 : ℝ) / 2) + (1 / 2 - 3 * (100 / 1327) - η) ≤ 1 / 2 - δ := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem original_uniform_limit {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ η0 : ℝ, 0 < η0 ∧ η0 ≤ 1 / 100 ∧
      ∀ η : ℝ, 0 < η → η < η0 →
      ∀ f : ℝ × ℝ → ℝ, Measurable f →
        (∀ z ∈ originalEnvelope, ‖f z‖ ≤ K) →
        |originalMass f 0 - originalMass f η| < ε := by
  let C : ℝ := 4 * K * ((25 / 206 : ℝ) - (100 / 1327) / 2)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num) hK) (by norm_num)
  refine ⟨min (1 / 100) (ε / (C + 1)), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  intro η hη hη0 f hf hb
  have hηhi : η ≤ 1 / 100 := hη0.le.trans (min_le_left _ _)
  have hsmall : η * (C + 1) < ε :=
    (lt_div_iff₀ (by positivity : 0 < C + 1)).mp
      (hη0.trans_le (min_le_right _ _))
  have he := original_uniform_error hη.le hηhi hf hb
  change |originalMass f 0 - originalMass f η| ≤ C * η at he
  nlinarith

end Wu18938Campaign.M5.StrictCorner
