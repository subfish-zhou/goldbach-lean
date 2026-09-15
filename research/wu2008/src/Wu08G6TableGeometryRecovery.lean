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

/-- Missing support is not an endpoint artifact. The exact rational witness
is structural, not a search point, and does not estimate an integral. -/
theorem explicit_missing_point :
    ((alpha + (1 / 4 - 2 * alpha)) / 2,
      (1 / 4 + (1 / 2 - 2 * alpha - (alpha + (1 / 4 - 2 * alpha)) / 2)) / 2)
        ∈ publishedReducedDomain ∧
    ((alpha + (1 / 4 - 2 * alpha)) / 2,
      (1 / 4 + (1 / 2 - 2 * alpha - (alpha + (1 / 4 - 2 * alpha)) / 2)) / 2)
        ∉ StaircaseShrink.domain 0 := by
  rw [actual_domain_eq_quarter_cut]
  norm_num [publishedReducedDomain, alpha, beta]

/-- At fixed u the quarter cut changes the lower x endpoint, not the height. -/
theorem quarter_cut_in_u {x r : ℝ} :
    1 / 2 - x - alpha * r ≤ 1 / 4 ↔ 1 / 4 - alpha * r ≤ x := by
  constructor <;> intro h <;> linarith

/-- The lost lower-end fibre disappears exactly at 927/400; only the first
three whole h cells and the beginning of the fourth are affected. -/
theorem missing_fibre_range {r : ℝ} :
    alpha < 1 / 4 - alpha * r ↔ r < 927 / 400 := by
  norm_num [alpha]
  constructor <;> intro h <;> linarith

theorem crossover_cell :
    (23 : ℝ) / 10 < 927 / 400 ∧ (927 : ℝ) / 400 < 24 / 10 := by
  norm_num

/-- The factor four in the original (x,y) kernel becomes eight after the
absolute Jacobian alpha. This is only a pointwise identity, not an unproved
integral change-of-variables assertion. -/
theorem jacobian_kernel {x r : ℝ} (hx : 0 < x) (hr : 0 < r)
    (hy : 0 < 1 / 2 - x - alpha * r) :
    4 * alpha / (x * (1 / 2 - x - alpha * r) * (alpha * r)) =
      8 / (x * r * (1 - 2 * x - 2 * alpha * r)) := by
  have ha := alpha_pos
  have hz : 0 < 1 - 2 * x - 2 * alpha * r := by linarith
  field_simp [hx.ne', hr.ne', ha.ne', hy.ne', hz.ne']
  ring

/-- Cinf is the exact existing quarter-cut evaluator. It is not the published
8 sum g6_i h_i, even if its heights are later proved to dominate the table. -/
theorem Cinf_literal :
    FeedbackLimit.Cinf = 4 * ∫ v : ℝ × ℝ,
      if v ∈ publishedReducedDomain ∩ {v | v.2 ≤ 1 / 4}
      then kernel (profile FeedbackLimit.Winf) v.1 v.2 else 0 := by
  simp only [FeedbackLimit.Cinf, Gamma, uniform, actual_domain_eq_quarter_cut]

end
end Wu08G6TableGeometryRecovery
