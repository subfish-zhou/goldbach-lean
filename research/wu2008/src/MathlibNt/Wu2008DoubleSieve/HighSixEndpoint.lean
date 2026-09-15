import MathlibNt.Wu2008DoubleSieve.HighSixTotalMass

namespace Wu2008DoubleSieve.HighSix
open Finset Real Filter Set
open scoped Classical Topology

/-- The small signed-density tolerance is selected internally, before all
thresholds and before N,p,q. No numerical integral value is required. -/
theorem normalized_main_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N → Even N →
        J*B6 N δ-ε*truncatedSixthMassScale N ≤ normalizedMain N δ η := by
  let η := min 1 (ε/(3840*(|kernelMass|+1)))
  have hk : 0 < |kernelMass|+1 := by positivity
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηbound : η*(3840*(|kernelMass|+1)) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hcost : 4*η*|kernelMass|+ε/960 ≤ ε/480 := by
    have haux : 0 ≤ η := hη.le
    nlinarith
  obtain ⟨T1,hT14,hT1⟩ := normalized_integral_relative hδ hδhi hη.le hη1
    (show 0 < ε/960 by positivity)
  obtain ⟨T2,_,hT2⟩ := B6_total_mass hδ hδhi
  refine ⟨η,hη,hη1,max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hi := hT1 N (by omega) he
  have hm := hT2 N (by omega) he
  have hs : 0 ≤ truncatedSixthMassScale N := by
    have hC := (wuSingularSeries_pos N (by omega : 0 < N)).le
    unfold truncatedSixthMassScale
    positivity
  have hfee : (4*η*kernelMass+ε/960)*B6 N δ ≤ ε*truncatedSixthMassScale N := by
    calc
      _ ≤ (4*η*|kernelMass|+ε/960)*B6 N δ := by
        apply mul_le_mul_of_nonneg_right _ hm.1
        have := mul_le_mul_of_nonneg_left (le_abs_self kernelMass) (show 0 ≤ 4*η by positivity)
        linarith
      _ ≤ (4*η*|kernelMass|+ε/960)*(480*truncatedSixthMassScale N) :=
        mul_le_mul_of_nonneg_left hm.2 (by positivity)
      _ ≤ (ε/480)*(480*truncatedSixthMassScale N) :=
        mul_le_mul_of_nonneg_right hcost (by positivity)
      _ = _ := by ring
  nlinarith

/-- Literal high-six Omega2 endpoint: the full moving main, its signed
normalization fee, divisor deletion, total mass, and BV are all paid. -/
theorem omega2_integral_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      J*B6 N δ-ε*truncatedSixthMassScale N ≤ O2 N δ := by
  obtain ⟨η,hη,hη1,T1,hT14,hT1⟩ := normalized_main_paid hδ hδhi (half_pos hε)
  obtain ⟨T2,_,hT2⟩ := omega2_normalized_paid hδ hδhi hη hη1 (half_pos hε)
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hm := hT1 N (by omega) he
  have ho := hT2 N (by omega) he
  linarith

/-- Actual finite first-mother consumption, leaving the positive O1 and O3
terms untouched. This theorem makes no claim about their analytic estimates. -/
theorem count_integral_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      2*C6 N ≤ O1 N δ-J*B6 N δ+O3 N δ+ε*truncatedSixthMassScale N := by
  obtain ⟨T,hT4,hT⟩ := omega2_integral_paid hδ hδhi hε
  refine ⟨T,hT4,?_⟩
  intro N hN he
  have ho := hT N hN he
  have hm := count_finite (by omega : 2 ≤ N) hδ hδhi
  linarith

end Wu2008DoubleSieve.HighSix
