import MathlibNt.Wu2008DoubleSieve.Omega3ElementaryRegularity

namespace Wu2008DoubleSieve.Omega3ElementaryEnvelope
open Set MeasureTheory SecondFunctionalGeometricMass

/-- Whole original nested integral comparison before taking any supremum. -/
theorem integral_le {s t φ : ℝ} (hs : 19/8 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hφ : 2 ≤ φ) :
    omega3XIntegral s t φ ≤ (4/7) * Elementary.elementaryMomentOne 1 (1/t) (1/s) := by
  have hs0 : 0 < s := by linarith
  have ht0 := hs0.trans_le hst
  have hl : (1/10 : ℝ) ≤ 1/t := one_div_le_one_div_of_le ht0 ht
  have hl0 : (0 : ℝ) < 1/t := by positivity
  have hlh := one_div_le_one_div_of_le hs0 hst
  have hinner (a : ℝ) (ha : a ∈ Icc (1/t) (1/s))
      (b : ℝ) (hb : b ∈ Icc a (1/s)) :
      (∫ c in b..(1/s), omega3XIntegralKernel φ a b c) ≤
        (4/7) * (∫ c in b..(1/s), (1 : ℝ)/(a*b^2*c)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hb.2
      (omega3XIntegralKernel_intervalIntegrable (hl.trans ha.1)
        ((hl.trans ha.1).trans hb.1) hb.2)
      ((Omega3ElementaryRegularity.kernel_integrable (hl.trans ha.1)
        ((hl.trans ha.1).trans hb.1) hb.2).const_mul _)
    intro c hc
    exact Omega3ElementaryGate.kernel_le hs hφ ha.2 hb.2 hc.2
      (hl0.trans_le ha.1) ((hl0.trans_le ha.1).trans_le hb.1)
      (((hl0.trans_le ha.1).trans_le hb.1).trans_le hc.1)
  have hmiddle (a : ℝ) (ha : a ∈ Icc (1/t) (1/s)) :
      (∫ b in a..(1/s), ∫ c in b..(1/s), omega3XIntegralKernel φ a b c) ≤
        (4/7) * (∫ b in a..(1/s), ∫ c in b..(1/s), (1 : ℝ)/(a*b^2*c)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ha.2
      (omega3XIntegral_inner_intervalIntegrable (hl.trans ha.1) ha.2)
      ((Omega3ElementaryRegularity.inner_integrable (hl.trans ha.1) ha.2).const_mul _)
      (hinner a ha)
  calc
    _ ≤ (4/7) * (∫ a in (1/t)..(1/s), ∫ b in a..(1/s), ∫ c in b..(1/s),
        (1 : ℝ)/(a*b^2*c)) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on hlh
        (omega3XIntegral_middle_intervalIntegrable hl hlh)
        ((Omega3ElementaryRegularity.middle_integrable hl hlh).const_mul _) hmiddle
    _ = _ := by rw [Omega3ElementaryMass.nested_eq_elementary hl0 hlh]

/-- The unchanged unbounded phi envelope, with both original endpoints. -/
theorem envelope_le {s t : ℝ} (hs : 19/8 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    omega3XIntegralEnvelope s t ≤ (4/7) * Elementary.elementaryMomentOne 1 (1/t) (1/s) := by
  apply csSup_le
  · exact ⟨omega3XIntegral s t 2, mem_image_of_mem _ (show (2 : ℝ) ∈ Ici 2 by simp)⟩
  · rintro y ⟨φ,hφ,rfl⟩
    exact integral_le hs hst ht hφ

/-- The equal-endpoint case is kept, not excluded by a strict width hypothesis. -/
theorem degenerate {s : ℝ} (hs : 0 < s) :
    omega3XIntegralEnvelope s s =
      (4/7) * Elementary.elementaryMomentOne 1 (1/s) (1/s) := by
  rw [omega3XIntegralEnvelope_self, Elementary.elementaryMomentOne_self 1 (by positivity), mul_zero]

/-- Every actual source phi is supplied by the original fixed-delta source theorem. -/
theorem actual_source_integral_le {i k N d : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hs : 19/8 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    0 ≤ omega3XIntegral s t (omega3XPhi N d δ) ∧
    omega3XIntegral s t (omega3XPhi N d δ) ≤
      (4/7) * Elementary.elementaryMomentOne 1 (1/t) (1/s) := by
  have h := omega3XIntegral_source_le_envelope hN hδ hδhi hb hd
    (show 2 ≤ s by linarith) hst ht
  exact ⟨h.1,h.2.trans (envelope_le hs hst ht)⟩

end Wu2008DoubleSieve.Omega3ElementaryEnvelope
