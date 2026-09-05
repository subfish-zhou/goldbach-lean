import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceFinal

namespace MathlibNt.SieveTheory

/-- The parameter inequalities chosen on Suzuki p.81, equations (14.3) and
(14.4).  Keeping them together prevents later consumers from silently assuming
extra size conditions on `Θ`. -/
structure Claim145SourceParameterPacket (Δ₀ Δ d Θ : ℝ) : Prop where
  delta0_le_one : Δ₀ ≤ 1
  delta_nonneg : 0 ≤ Δ
  d_pos : 0 < d
  theta_pos : 0 < Θ
  equation14_3 : 2 / d < 1 / Θ
  equation14_4 : 2 / Θ + 3 / d < Δ₀ - Δ

/-- Equation (14.4), together with the source range `Δ₀ ≤ 1` and `Δ ≥ 0`,
forces the auxiliary exponent to exceed two.  In particular the `1 ≤ Θ`
condition used by the uniform Case-B logarithmic bookkeeping is not an added
hypothesis. -/
theorem Claim145SourceParameterPacket.two_lt_theta
    {Δ₀ Δ d Θ : ℝ} (h : Claim145SourceParameterPacket Δ₀ Δ d Θ) :
    2 < Θ := by
  have hthree : 0 < 3 / d := div_pos (by norm_num) h.d_pos
  have hgap_le : Δ₀ - Δ ≤ 1 := by linarith [h.delta0_le_one, h.delta_nonneg]
  have htwo_div : 2 / Θ < 1 := by linarith [h.equation14_4]
  rw [div_lt_iff₀ h.theta_pos] at htwo_div
  simpa using htwo_div

 theorem Claim145SourceParameterPacket.one_le_theta
    {Δ₀ Δ d Θ : ℝ} (h : Claim145SourceParameterPacket Δ₀ Δ d Θ) :
    1 ≤ Θ := (show (1 : ℝ) < 2 by norm_num).trans h.two_lt_theta |>.le

/-- The same packet supplies the positive high-coordinate exponent gap. -/
theorem Claim145SourceParameterPacket.highS_gap
    {Δ₀ Δ d Θ : ℝ} (h : Claim145SourceParameterPacket Δ₀ Δ d Θ) :
    0 < d - 2 * Θ := by
  have := h.equation14_3
  rw [div_lt_div_iff₀ h.d_pos h.theta_pos] at this
  linarith

/-- Exact specialized source packet on Suzuki p.81 for `κ = κ̂ = 1`, where
`Δ₀ = 1`. -/
structure SuzukiClaim145SourceParameters (d Δ Θ : ℝ) : Prop where
  hDelta_pos : 0 < Δ
  hDelta_lt : Δ < 1
  h14_1 : 7 / (1 - Δ) < d
  hTheta_pos : 0 < Θ
  h14_3 : 2 / d < 1 / Θ
  h14_4 : 2 / Θ + 3 / d < 1 - Δ

namespace SuzukiClaim145SourceParameters

variable {d Δ Θ : ℝ}

theorem d_pos (h : SuzukiClaim145SourceParameters d Δ Θ) : 0 < d := by
  have hden : 0 < 1 - Δ := sub_pos.mpr h.hDelta_lt
  exact (div_pos (by norm_num) hden).trans h.h14_1

theorem two_lt_theta (h : SuzukiClaim145SourceParameters d Δ Θ) : 2 < Θ := by
  have hthree : 0 < 3 / d := div_pos (by norm_num) h.d_pos
  have hfrac : 2 / Θ < 1 := by linarith [h.h14_4, h.hDelta_pos]
  simpa only [one_mul] using (div_lt_iff₀ h.hTheta_pos).mp hfrac

theorem one_le_theta (h : SuzukiClaim145SourceParameters d Δ Θ) : 1 ≤ Θ :=
  h.two_lt_theta.le.trans' (by norm_num)

theorem toGeneric (h : SuzukiClaim145SourceParameters d Δ Θ) :
    Claim145SourceParameterPacket 1 Δ d Θ where
  delta0_le_one := le_rfl
  delta_nonneg := h.hDelta_pos.le
  d_pos := h.d_pos
  theta_pos := h.hTheta_pos
  equation14_3 := h.h14_3
  equation14_4 := by simpa using h.h14_4

end SuzukiClaim145SourceParameters


end MathlibNt.SieveTheory
