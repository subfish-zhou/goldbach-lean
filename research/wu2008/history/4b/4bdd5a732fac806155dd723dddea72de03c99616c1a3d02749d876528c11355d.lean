import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralDomain
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The actual Buchstab integral kernel

Wu04, arXiv TeX lines 2240–2259. Continuity, not differentiability at the
Buchstab fold at two, is used throughout. A globally continuous extension
agrees with the actual kernel on the whole source exponent cube.
-/

namespace Wu2008DoubleSieve

open Real Set MeasureTheory LiLiuPrereqBuchstab

noncomputable def omega3XIntegralKernel (φ a b c : ℝ) : ℝ :=
  buchstab ((φ - a - b - c) / b) / (a * b ^ 2 * c)

noncomputable def omega3XIntegral (s t φ : ℝ) : ℝ :=
  ∫ a in (1 / t)..(1 / s), ∫ b in a..(1 / s), ∫ c in b..(1 / s),
    omega3XIntegralKernel φ a b c

/-- A positive-coordinate extension is used only for continuity proofs.
On the source cube no clamping takes place. -/
noncomputable def omega3XIntegralKernelExtension (φ a b c : ℝ) : ℝ :=
  omega3XIntegralKernel φ (max (1 / 10) a) (max (1 / 10) b) (max (1 / 10) c)

theorem omega3XIntegralKernelExtension_eq {φ a b c : ℝ}
    (ha : 1 / 10 ≤ a) (hb : 1 / 10 ≤ b) (hc : 1 / 10 ≤ c) :
    omega3XIntegralKernelExtension φ a b c = omega3XIntegralKernel φ a b c := by
  simp only [omega3XIntegralKernelExtension, max_eq_right ha, max_eq_right hb,
    max_eq_right hc]

theorem omega3XIntegralKernelExtension_continuous :
    Continuous (fun p : ℝ × ℝ × ℝ × ℝ =>
      omega3XIntegralKernelExtension p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold omega3XIntegralKernelExtension omega3XIntegralKernel
  apply Continuous.div
  · apply continuous_buchstab.comp
    fun_prop (disch := intro p; positivity)
  · fun_prop
  · intro p
    positivity

/-- Joint uniform continuity is uniform in phi as well as all three exponents. -/
theorem omega3XIntegralKernel_uniformContinuousOn (M : ℝ) :
    UniformContinuousOn
      (fun p : ℝ × ℝ × ℝ × ℝ => omega3XIntegralKernel p.1 p.2.1 p.2.2.1 p.2.2.2)
      (Icc 2 M ×ˢ (Icc (1 / 10) (1 / 2) ×ˢ
        (Icc (1 / 10) (1 / 2) ×ˢ Icc (1 / 10) (1 / 2)))) := by
  have hcompact : IsCompact
      (Icc (2 : ℝ) M ×ˢ (Icc (1 / 10 : ℝ) (1 / 2) ×ˢ
        (Icc (1 / 10 : ℝ) (1 / 2) ×ˢ Icc (1 / 10 : ℝ) (1 / 2)))) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  apply (hcompact.uniformContinuousOn_of_continuous
    omega3XIntegralKernelExtension_continuous.continuousOn).congr
  intro p hp
  exact omega3XIntegralKernelExtension_eq hp.2.1.1 hp.2.2.1.1 hp.2.2.2.1

theorem omega3XIntegralKernel_continuousOn (M : ℝ) :
    ContinuousOn
      (fun p : ℝ × ℝ × ℝ × ℝ => omega3XIntegralKernel p.1 p.2.1 p.2.2.1 p.2.2.2)
      (Icc 2 M ×ˢ (Icc (1 / 10) (1 / 2) ×ˢ
        (Icc (1 / 10) (1 / 2) ×ˢ Icc (1 / 10) (1 / 2)))) :=
  (omega3XIntegralKernel_uniformContinuousOn M).continuousOn

/-- A finite phi-independent majorant; it remains valid at u=1. -/
theorem omega3XIntegralKernel_bounds {φ a b c : ℝ} (hφ : 2 ≤ φ)
    (ha : a ∈ Icc (1 / 10) (1 / 2))
    (hb : b ∈ Icc (1 / 10) (1 / 2))
    (hc : c ∈ Icc (1 / 10) (1 / 2)) :
    0 ≤ omega3XIntegralKernel φ a b c ∧ omega3XIntegralKernel φ a b c ≤ 10000 := by
  have hu := (omega3X_argument_bounds hφ ha hb hc).2.2
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < b := by linarith [hb.1]
  have hc0 : 0 < c := by linarith [hc.1]
  have hden : 1 / 10000 ≤ a * b ^ 2 * c := by
    calc
      _ = (1 / 10 : ℝ) * (1 / 10) ^ 2 * (1 / 10) := by norm_num
      _ ≤ _ := by gcongr <;> first | exact ha.1 | exact hb.1 | exact hc.1
  unfold omega3XIntegralKernel
  refine ⟨div_nonneg (by linarith [one_half_le_buchstab hu]) (by positivity), ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < a * b ^ 2 * c)).mpr
  linarith [buchstab_le_one hu]

theorem omega3XIntegral_self (s φ : ℝ) : omega3XIntegral s s φ = 0 := by
  simp [omega3XIntegral]

end Wu2008DoubleSieve
