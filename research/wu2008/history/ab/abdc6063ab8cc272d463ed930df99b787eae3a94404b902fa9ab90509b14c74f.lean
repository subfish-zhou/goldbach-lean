import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralKernel

/-!
# Moving-bound regularity of the actual nested integral

The continuous extension makes all moving-bound operations legitimate.
Equality on every closed fibre transfers continuity and integrability to
the actual kernel. No convention assigning zero to nonintegrable functions
is used to obtain the estimates.
-/

namespace Wu2008DoubleSieve

open Real Set MeasureTheory

private theorem continuous_moving_integral {X : Type*} [TopologicalSpace X]
    {f : X → ℝ → ℝ} {l h : X → ℝ}
    (hf : Continuous f.uncurry) (hl : Continuous l) (hh : Continuous h) :
    Continuous (fun x => ∫ v in l x..h x, f x v) := by
  have hhi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf hh
  have hlo := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf hl
  convert hhi.sub hlo using 1
  ext x
  exact (intervalIntegral.integral_interval_sub_left
    ((hf.uncurry_left x).intervalIntegrable 0 (h x))
    ((hf.uncurry_left x).intervalIntegrable 0 (l x))).symm

theorem omega3XIntegral_innerExtension_continuous :
    Continuous (fun p : ℝ × ℝ × ℝ × ℝ =>
      ∫ c in p.2.2.2..p.2.1,
        omega3XIntegralKernelExtension p.1 p.2.2.1 p.2.2.2 c) := by
  apply continuous_moving_integral
    (X := ℝ × ℝ × ℝ × ℝ)
    (l := fun p => p.2.2.2) (h := fun p => p.2.1)
    (f := fun p c => omega3XIntegralKernelExtension p.1 p.2.2.1 p.2.2.2 c)
  · exact omega3XIntegralKernelExtension_continuous.comp
      (f := fun p : (ℝ × ℝ × ℝ × ℝ) × ℝ =>
        (p.1.1, p.1.2.2.1, p.1.2.2.2, p.2))
      (show Continuous (fun p : (ℝ × ℝ × ℝ × ℝ) × ℝ =>
        (p.1.1, p.1.2.2.1, p.1.2.2.2, p.2)) by fun_prop)
  · fun_prop
  · fun_prop

theorem omega3XIntegral_middleExtension_continuous :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      ∫ b in p.2.2..p.2.1, ∫ c in b..p.2.1,
        omega3XIntegralKernelExtension p.1 p.2.2 b c) := by
  apply continuous_moving_integral
    (X := ℝ × ℝ × ℝ)
    (l := fun p => p.2.2) (h := fun p => p.2.1)
    (f := fun p b => ∫ c in b..p.2.1, omega3XIntegralKernelExtension p.1 p.2.2 b c)
  · exact omega3XIntegral_innerExtension_continuous.comp
      (f := fun p : (ℝ × ℝ × ℝ) × ℝ =>
        (p.1.1, p.1.2.1, p.1.2.2, p.2))
      (show Continuous (fun p : (ℝ × ℝ × ℝ) × ℝ =>
        (p.1.1, p.1.2.1, p.1.2.2, p.2)) by fun_prop)
  · fun_prop
  · fun_prop

noncomputable def omega3XIntegralExtension (l h φ : ℝ) : ℝ :=
  ∫ a in l..h, ∫ b in a..h, ∫ c in b..h, omega3XIntegralKernelExtension φ a b c

theorem omega3XIntegralExtension_continuous :
    Continuous (fun p : ℝ × ℝ × ℝ => omega3XIntegralExtension p.1 p.2.1 p.2.2) := by
  unfold omega3XIntegralExtension
  apply continuous_moving_integral
    (X := ℝ × ℝ × ℝ)
    (l := fun p => p.1) (h := fun p => p.2.1)
    (f := fun p a => ∫ b in a..p.2.1, ∫ c in b..p.2.1,
      omega3XIntegralKernelExtension p.2.2 a b c)
  · exact omega3XIntegral_middleExtension_continuous.comp
      (f := fun p : (ℝ × ℝ × ℝ) × ℝ =>
        (p.1.2.2, p.1.2.1, p.2))
      (show Continuous (fun p : (ℝ × ℝ × ℝ) × ℝ =>
        (p.1.2.2, p.1.2.1, p.2)) by fun_prop)
  · fun_prop
  · fun_prop

theorem omega3XIntegral_innerExtension_eq {φ a b h : ℝ}
    (ha : 1 / 10 ≤ a) (hb : 1 / 10 ≤ b) (hbh : b ≤ h) :
    (∫ c in b..h, omega3XIntegralKernelExtension φ a b c) =
      ∫ c in b..h, omega3XIntegralKernel φ a b c := by
  apply intervalIntegral.integral_congr
  intro c hc
  rw [uIcc_of_le hbh] at hc
  exact omega3XIntegralKernelExtension_eq ha hb (hb.trans hc.1)

theorem omega3XIntegral_middleExtension_eq {φ a h : ℝ}
    (ha : 1 / 10 ≤ a) (hah : a ≤ h) :
    (∫ b in a..h, ∫ c in b..h, omega3XIntegralKernelExtension φ a b c) =
      ∫ b in a..h, ∫ c in b..h, omega3XIntegralKernel φ a b c := by
  apply intervalIntegral.integral_congr
  intro b hb
  rw [uIcc_of_le hah] at hb
  exact omega3XIntegral_innerExtension_eq ha (ha.trans hb.1) hb.2

theorem omega3XIntegralExtension_eq {φ l h : ℝ}
    (hl : 1 / 10 ≤ l) (hlh : l ≤ h) :
    omega3XIntegralExtension l h φ =
      ∫ a in l..h, ∫ b in a..h, ∫ c in b..h, omega3XIntegralKernel φ a b c := by
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le hlh] at ha
  exact omega3XIntegral_middleExtension_eq (hl.trans ha.1) ha.2

theorem omega3XIntegral_inner_continuousOn {φ a l h : ℝ}
    (ha : 1 / 10 ≤ a) (hl : 1 / 10 ≤ l) :
    ContinuousOn (fun b => ∫ c in b..h, omega3XIntegralKernel φ a b c) (Icc l h) := by
  have hcont : Continuous (fun b => ∫ c in b..h,
      omega3XIntegralKernelExtension φ a b c) :=
    omega3XIntegral_innerExtension_continuous.comp
      (show Continuous (fun b : ℝ => (φ, h, a, b)) by fun_prop)
  apply hcont.continuousOn.congr
  intro b hb
  exact (omega3XIntegral_innerExtension_eq ha (hl.trans hb.1) hb.2).symm

theorem omega3XIntegral_middle_continuousOn {φ l h : ℝ} (hl : 1 / 10 ≤ l) :
    ContinuousOn (fun a => ∫ b in a..h, ∫ c in b..h,
      omega3XIntegralKernel φ a b c) (Icc l h) := by
  have hcont : Continuous (fun a => ∫ b in a..h, ∫ c in b..h,
      omega3XIntegralKernelExtension φ a b c) :=
    omega3XIntegral_middleExtension_continuous.comp
      (show Continuous (fun a : ℝ => (φ, h, a)) by fun_prop)
  apply hcont.continuousOn.congr
  intro a ha
  exact (omega3XIntegral_middleExtension_eq (hl.trans ha.1) ha.2).symm

theorem omega3XIntegralKernel_intervalIntegrable {φ a b h : ℝ}
    (ha : 1 / 10 ≤ a) (hb : 1 / 10 ≤ b) (hbh : b ≤ h) :
    IntervalIntegrable (omega3XIntegralKernel φ a b) volume b h := by
  have hcont : Continuous (fun c => omega3XIntegralKernelExtension φ a b c) :=
    omega3XIntegralKernelExtension_continuous.comp
      (f := fun c : ℝ => (φ, a, b, c))
      (show Continuous (fun c : ℝ => (φ, a, b, c)) by fun_prop)
  apply ContinuousOn.intervalIntegrable
  apply hcont.continuousOn.congr
  intro c hc
  rw [uIcc_of_le hbh] at hc
  exact (omega3XIntegralKernelExtension_eq ha hb (hb.trans hc.1)).symm

theorem omega3XIntegral_inner_intervalIntegrable {φ a h : ℝ}
    (ha : 1 / 10 ≤ a) (hah : a ≤ h) :
    IntervalIntegrable (fun b => ∫ c in b..h, omega3XIntegralKernel φ a b c)
      volume a h := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hah]
  exact omega3XIntegral_inner_continuousOn ha ha

theorem omega3XIntegral_middle_intervalIntegrable {φ l h : ℝ}
    (hl : 1 / 10 ≤ l) (hlh : l ≤ h) :
    IntervalIntegrable (fun a => ∫ b in a..h, ∫ c in b..h,
      omega3XIntegralKernel φ a b c) volume l h := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hlh]
  exact omega3XIntegral_middle_continuousOn hl

/-- Joint continuity includes the moving and degenerate source endpoints. -/
theorem omega3XIntegral_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => omega3XIntegral p.1 p.2.1 p.2.2)
      {p | 2 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ 10} := by
  have hmap : ContinuousOn (fun p : ℝ × ℝ × ℝ => (1 / p.2.1, 1 / p.1, p.2.2))
      {p | 2 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ 10} := by
    apply ContinuousOn.prodMk
    · apply continuousOn_const.div continuous_snd.fst.continuousOn
      intro p hp
      dsimp at hp
      linarith [hp.1, hp.2.1]
    · apply ContinuousOn.prodMk
      · apply continuousOn_const.div continuous_fst.continuousOn
        intro p hp
        dsimp at hp
        linarith [hp.1]
      · fun_prop
  apply (omega3XIntegralExtension_continuous.comp_continuousOn hmap).congr
  intro p hp
  have hs0 : 0 < p.1 := by linarith [hp.1]
  have ht0 : 0 < p.2.1 := hs0.trans_le hp.2.1
  exact (omega3XIntegralExtension_eq
    (one_div_le_one_div_of_le ht0 hp.2.2)
    (one_div_le_one_div_of_le hs0 hp.2.1)).symm

end Wu2008DoubleSieve
