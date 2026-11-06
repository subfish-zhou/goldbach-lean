import FeedbackIntegral

/-! Literal distinction between Wu08's 21-cell lower-integral domain and
Cinf's actual quarter-cut source domain. No numerical log or integration. -/
namespace Wu08G6TableGeometryRecovery
open Set QuarterTrim DirectFiniteF6
open scoped Classical
noncomputable section

/-- The two displayed one-dimensional integrals at Wu08 TeX 2086--2095
are obtained from this triangle (not its quarter-cut subset). -/
def publishedReducedDomain : Set (ℝ × ℝ) :=
  {v | alpha ≤ v.1 ∧ v.1 ≤ beta ∧ beta ≤ v.2 ∧
    v.1 + v.2 ≤ 1 / 2 - 2 * alpha}

theorem actual_domain_eq_quarter_cut :
    StaircaseShrink.domain 0 = publishedReducedDomain ∩ {v | v.2 ≤ 1 / 4} := by
  ext v
  rcases v with ⟨x,y⟩
  rw [StaircaseShrink.domain_iff]
  simp only [publishedReducedDomain, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨ha,hb,hc,hd,he⟩
    exact ⟨⟨ha,hb,hc,by linarith⟩,by linarith⟩
  · rintro ⟨⟨ha,hb,hc,he⟩,hd⟩
    exact ⟨ha,hb,hc,by linarith,by linarith⟩







end
end Wu08G6TableGeometryRecovery
