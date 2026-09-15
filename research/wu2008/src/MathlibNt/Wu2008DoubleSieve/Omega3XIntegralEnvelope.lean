import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralKernelIntegrability

/-!
# A finite source-compatible upper envelope

Wu04, arXiv TeX lines 2240–2259. The supremum is over the unbounded
parameter range phi >= 2 and retains both endpoint parameters. Finiteness
comes from the global Buchstab bound, not an assertion that a maximum on
the unbounded phi-domain is attained.
-/

namespace Wu2008DoubleSieve

open Real Set MeasureTheory

private theorem integral_box_bounds {φ l h : ℝ}
    (hφ : 2 ≤ φ) (hl : 1 / 10 ≤ l) (hlh : l ≤ h) (hh : h ≤ 1 / 2) :
    0 ≤ (∫ a in l..h, ∫ b in a..h, ∫ c in b..h, omega3XIntegralKernel φ a b c) ∧
    (∫ a in l..h, ∫ b in a..h, ∫ c in b..h, omega3XIntegralKernel φ a b c) ≤
      10000 * (h - l) ^ 3 := by
  have hwidth : 0 ≤ h - l := sub_nonneg.mpr hlh
  have hinner (a : ℝ) (ha : a ∈ Icc l h) (b : ℝ) (hb : b ∈ Icc a h) :
      0 ≤ (∫ c in b..h, omega3XIntegralKernel φ a b c) ∧
      (∫ c in b..h, omega3XIntegralKernel φ a b c) ≤ 10000 * (h - l) := by
    have hpoint (c : ℝ) (hc : c ∈ Icc b h) :=
      omega3XIntegralKernel_bounds hφ
        ⟨hl.trans ha.1, ha.2.trans hh⟩
        ⟨(hl.trans ha.1).trans hb.1, hb.2.trans hh⟩
        ⟨((hl.trans ha.1).trans hb.1).trans hc.1, hc.2.trans hh⟩
    refine ⟨intervalIntegral.integral_nonneg hb.2 (fun c hc => (hpoint c hc).1), ?_⟩
    calc
      _ ≤ ∫ _c in b..h, (10000 : ℝ) :=
        intervalIntegral.integral_mono_on hb.2
          (omega3XIntegralKernel_intervalIntegrable (hl.trans ha.1)
            ((hl.trans ha.1).trans hb.1) hb.2)
          (continuous_const.intervalIntegrable _ _) (fun c hc => (hpoint c hc).2)
      _ = (h - b) * 10000 := by simp
      _ ≤ _ := by linarith [ha.1, hb.1]
  have hmiddle (a : ℝ) (ha : a ∈ Icc l h) :
      0 ≤ (∫ b in a..h, ∫ c in b..h, omega3XIntegralKernel φ a b c) ∧
      (∫ b in a..h, ∫ c in b..h, omega3XIntegralKernel φ a b c) ≤
        10000 * (h - l) ^ 2 := by
    refine ⟨intervalIntegral.integral_nonneg ha.2
      (fun b hb => (hinner a ha b hb).1), ?_⟩
    calc
      _ ≤ ∫ _b in a..h, 10000 * (h - l) :=
        intervalIntegral.integral_mono_on ha.2
          (omega3XIntegral_inner_intervalIntegrable (hl.trans ha.1) ha.2)
          (continuous_const.intervalIntegrable _ _) (fun b hb => (hinner a ha b hb).2)
      _ = (h - a) * (10000 * (h - l)) := by simp; ring
      _ ≤ (h - l) * (10000 * (h - l)) :=
        mul_le_mul_of_nonneg_right (by linarith [ha.1]) (by positivity)
      _ = _ := by ring
  refine ⟨intervalIntegral.integral_nonneg hlh (fun a ha => (hmiddle a ha).1), ?_⟩
  calc
    _ ≤ ∫ _a in l..h, 10000 * (h - l) ^ 2 :=
      intervalIntegral.integral_mono_on hlh
        (omega3XIntegral_middle_intervalIntegrable hl hlh)
        (continuous_const.intervalIntegrable _ _) (fun a ha => (hmiddle a ha).2)
    _ = _ := by simp; ring

/-- An additive bound vanishing cubically with the endpoint width. -/
theorem omega3XIntegral_bounds {s t φ : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) (hφ : 2 ≤ φ) :
    0 ≤ omega3XIntegral s t φ ∧
    omega3XIntegral s t φ ≤ 10000 * (1 / s - 1 / t) ^ 3 := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := hs0.trans_le hst
  exact integral_box_bounds hφ (one_div_le_one_div_of_le ht0 ht)
    (one_div_le_one_div_of_le hs0 hst)
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs)

theorem omega3XIntegral_nonneg {s t φ : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) (hφ : 2 ≤ φ) :
    0 ≤ omega3XIntegral s t φ :=
  (omega3XIntegral_bounds hs hst ht hφ).1

theorem omega3XIntegral_bddAbove {s t : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    BddAbove ((fun φ => omega3XIntegral s t φ) '' Ici 2) := by
  refine ⟨10000 * (1 / s - 1 / t) ^ 3, ?_⟩
  rintro y ⟨φ, hφ, rfl⟩
  exact (omega3XIntegral_bounds hs hst ht hφ).2

noncomputable def omega3XIntegralEnvelope (s t : ℝ) : ℝ :=
  sSup ((fun φ => omega3XIntegral s t φ) '' Ici 2)

theorem omega3XIntegral_le_envelope {s t φ : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) (hφ : 2 ≤ φ) :
    omega3XIntegral s t φ ≤ omega3XIntegralEnvelope s t :=
  le_csSup (omega3XIntegral_bddAbove hs hst ht) (mem_image_of_mem _ hφ)

theorem omega3XIntegralEnvelope_bounds {s t : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    0 ≤ omega3XIntegralEnvelope s t ∧
    omega3XIntegralEnvelope s t ≤ 10000 * (1 / s - 1 / t) ^ 3 := by
  refine ⟨(omega3XIntegral_nonneg hs hst ht (le_refl 2)).trans
    (omega3XIntegral_le_envelope hs hst ht (le_refl 2)), ?_⟩
  apply csSup_le
  · exact ⟨omega3XIntegral s t 2, mem_image_of_mem _ (show (2 : ℝ) ∈ Ici 2 by simp)⟩
  · rintro y ⟨φ, hφ, rfl⟩
    exact (omega3XIntegral_bounds hs hst ht hφ).2

theorem omega3XIntegralEnvelope_self (s : ℝ) : omega3XIntegralEnvelope s s = 0 := by
  have himage : ((fun φ => omega3XIntegral s s φ) '' Ici 2) = ({0} : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨φ, _, rfl⟩
      simp [omega3XIntegral_self]
    · intro hx
      have hx0 : x = 0 := mem_singleton_iff.mp hx
      exact ⟨2, (show (2 : ℝ) ∈ Ici 2 by simp), by simp [hx0, omega3XIntegral_self]⟩
  simp [omega3XIntegralEnvelope, himage]

/-- The envelope is applied at the phi of every actual supported d. -/
theorem omega3XIntegral_source_le_envelope {i k N d : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    0 ≤ omega3XIntegral s t (omega3XPhi N d δ) ∧
    omega3XIntegral s t (omega3XPhi N d δ) ≤ omega3XIntegralEnvelope s t := by
  have hφ := (omega3XPhi_source_bounds hN hδ hδhi hb hd).2.2.1
  have hgap : 0 < 2 * δ / (1 / 2 - δ) := by positivity
  have hφ2 : 2 ≤ omega3XPhi N d δ := by linarith
  exact ⟨omega3XIntegral_nonneg hs hst ht hφ2,
    omega3XIntegral_le_envelope hs hst ht hφ2⟩

end Wu2008DoubleSieve
