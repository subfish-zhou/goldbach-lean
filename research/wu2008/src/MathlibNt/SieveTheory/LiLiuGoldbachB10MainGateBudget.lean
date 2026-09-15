import MathlibNt.SieveTheory.LiLiuGoldbachB10ProductCount
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirectConductorWeight

noncomputable section

open scoped BigOperators
open Classical Finset
open AnalyticNumberTheory.LargeSieve

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableB10MainGateBudget (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The modulus-`d` loss from deleting the non-coprime part of the actual `C10`
product support. -/
noncomputable def gateLoss
    (N : ℕ) (b c : ℝ) (w : ℕ → ℝ) (d : ℕ) : ℝ :=
  |((d.totient : ℝ)⁻¹) *
    ∑ m ∈ goldbachC10ProductSupport N b c with ¬Nat.Coprime m d, w m|

theorem gateLoss_eq
    (N : ℕ) (b c : ℝ) (w : ℕ → ℝ) (d : ℕ) :
    gateLoss N b c w d =
      |(1 / (d.totient : ℝ)) *
        ∑ m ∈ goldbachC10ProductSupport N b c with ¬Nat.Coprime m d, w m| := by
  simp [gateLoss, one_div]

private theorem B10MainGateBudget_support_le
    {N : ℕ} {b c : ℝ} {m : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N b c) :
    m ≤ N := by
  rcases mem_goldbachC10ProductSupport_iff.mp hm with ⟨rs, hrs, hprod⟩
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨_, hsPrime, _, _, _, _, hsize⟩
  rw [← hprod, goldbachC10Prod]
  have hsone : 1 ≤ rs.2 := Nat.succ_le_of_lt hsPrime.pos
  have hsleSq : rs.2 ≤ rs.2 ^ 2 := by
    calc
      rs.2 = rs.2 * 1 := by simp
      _ ≤ rs.2 * rs.2 := by
        gcongr
      _ = rs.2 ^ 2 := by rw [pow_two]
  exact le_trans (Nat.mul_le_mul_left rs.1 hsleSq) hsize

private theorem B10MainGateBudget_support_mem_Icc
    {N : ℕ} {b c : ℝ} {m : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N b c) :
    m ∈ Finset.Icc 1 N := by
  exact Finset.mem_Icc.mpr
    ⟨Nat.succ_le_of_lt (goldbachC10ProductSupport_pos hm), B10MainGateBudget_support_le hm⟩

private theorem B10MainGateBudget_invTotient_prime_le_two_div
    {p : ℕ} (hp : p.Prime) :
    ((p.totient : ℝ)⁻¹) ≤ 2 / (p : ℝ) := by
  rw [Nat.totient_prime hp, Nat.cast_sub (Nat.succ_le_of_lt hp.pos), Nat.cast_one]
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast hp.two_le
  have hhalf : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by
    nlinarith
  have hhalfpos : 0 < (p : ℝ) / 2 := by
    positivity
  calc
    ((p : ℝ) - 1)⁻¹ ≤ ((p : ℝ) / 2)⁻¹ := inv_anti₀ hhalfpos hhalf
    _ = 2 / (p : ℝ) := by
      field_simp

private theorem B10MainGateBudget_invTotient_prime_le_two_div_b
    {p : ℕ} {b : ℝ} (hp : p.Prime) (hb : 0 < b) (hbp : b ≤ (p : ℝ)) :
    ((p.totient : ℝ)⁻¹) ≤ 2 / b := by
  calc
    ((p.totient : ℝ)⁻¹) ≤ 2 / (p : ℝ) :=
      B10MainGateBudget_invTotient_prime_le_two_div hp
    _ ≤ 2 / b := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hInv : ((p : ℝ)⁻¹) ≤ b⁻¹ := inv_anti₀ hb hbp
      nlinarith

private theorem B10MainGateBudget_bad_inverseTotientMass_le
    {N Q : ℕ} {b c : ℝ} {m : ℕ}
    (hQ : Q ≤ N) (hb : 0 < b)
    (hm : m ∈ goldbachC10ProductSupport N b c) :
    (∑ d ∈ Finset.Icc 1 Q, if ¬Nat.Coprime m d then ((d.totient : ℝ)⁻¹) else 0) ≤
      (4 / b) * conductorHarmonicFactor N ^ 2 := by
  rcases mem_goldbachC10ProductSupport_iff.mp hm with ⟨rs, hrs, hprod⟩
  rcases mem_goldbachC10Pairs_iff.mp hrs with
    ⟨hrPrime, hsPrime, _, hbr, hrc, hcs, _⟩
  have hbs : b ≤ (rs.2 : ℝ) := le_trans hbr (le_trans hrc hcs)
  calc
    (∑ d ∈ Finset.Icc 1 Q, if ¬Nat.Coprime m d then ((d.totient : ℝ)⁻¹) else 0)
      ≤ (∑ d ∈ Finset.Icc 1 Q,
          ((if rs.1 ∣ d then ((d.totient : ℝ)⁻¹) else 0) +
            (if rs.2 ∣ d then ((d.totient : ℝ)⁻¹) else 0))) := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hbad : ¬Nat.Coprime m d
          · have hdiv : rs.1 ∣ d ∨ rs.2 ∣ d := by
              by_cases hr : rs.1 ∣ d
              · exact Or.inl hr
              · right
                by_contra hs
                apply hbad
                rw [← hprod, goldbachC10Prod, Nat.coprime_mul_iff_left,
                  hrPrime.coprime_iff_not_dvd, hsPrime.coprime_iff_not_dvd]
                exact ⟨hr, hs⟩
            have hnonneg₁ : 0 ≤ if rs.1 ∣ d then ((d.totient : ℝ)⁻¹) else 0 := by
              split_ifs <;> positivity
            have hnonneg₂ : 0 ≤ if rs.2 ∣ d then ((d.totient : ℝ)⁻¹) else 0 := by
              split_ifs <;> positivity
            rcases hdiv with hr | hs
            · simp [hbad, hr]
              linarith
            · simp [hbad, hs]
              linarith
          · have hnonneg₁ : 0 ≤ if rs.1 ∣ d then ((d.totient : ℝ)⁻¹) else 0 := by
              split_ifs <;> positivity
            have hnonneg₂ : 0 ≤ if rs.2 ∣ d then ((d.totient : ℝ)⁻¹) else 0 := by
              split_ifs <;> positivity
            simp [hbad]
            linarith
    _ = directConductorWeight Q rs.1 + directConductorWeight Q rs.2 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
      rfl
    _ ≤ conductorHarmonicFactor Q ^ 2 / (rs.1.totient : ℝ) +
        conductorHarmonicFactor Q ^ 2 / (rs.2.totient : ℝ) := by
      exact add_le_add (directConductorWeight_le Q rs.1) (directConductorWeight_le Q rs.2)
    _ = conductorHarmonicFactor Q ^ 2 *
        (((rs.1.totient : ℝ)⁻¹) + ((rs.2.totient : ℝ)⁻¹)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    _ ≤ conductorHarmonicFactor Q ^ 2 * (4 / b) := by
      apply mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have hr :
          ((rs.1.totient : ℝ)⁻¹) ≤ 2 / b :=
        B10MainGateBudget_invTotient_prime_le_two_div_b hrPrime hb hbr
      have hs :
          ((rs.2.totient : ℝ)⁻¹) ≤ 2 / b :=
        B10MainGateBudget_invTotient_prime_le_two_div_b hsPrime hb hbs
      calc
        ((rs.1.totient : ℝ)⁻¹) + ((rs.2.totient : ℝ)⁻¹)
          ≤ 2 / b + 2 / b := add_le_add hr hs
        _ = 4 / b := by ring
    _ = (4 / b) * conductorHarmonicFactor Q ^ 2 := by
      ring
    _ ≤ (4 / b) * conductorHarmonicFactor N ^ 2 := by
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (sq_le_sq₀ (conductorHarmonicFactor_nonneg Q)
        (conductorHarmonicFactor_nonneg N)).2 (conductorHarmonicFactor_mono hQ)

private theorem B10MainGateBudget_weightMass_le
    {N : ℕ} {b c T : ℝ} {w : ℕ → ℝ}
    (hT : 0 ≤ T)
    (hw : ∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → |w m| ≤ T / (m : ℝ)) :
    ∑ m ∈ goldbachC10ProductSupport N b c, |w m| ≤
      T * conductorHarmonicFactor N := by
  calc
    ∑ m ∈ goldbachC10ProductSupport N b c, |w m|
      ≤ ∑ m ∈ goldbachC10ProductSupport N b c, T / (m : ℝ) := by
          apply Finset.sum_le_sum
          intro m hm
          exact hw hm
    _ = T * ∑ m ∈ goldbachC10ProductSupport N b c, (m : ℝ)⁻¹ := by
      simp [div_eq_mul_inv, mul_sum]
    _ ≤ T * conductorHarmonicFactor N := by
      apply mul_le_mul_of_nonneg_left ?_ hT
      unfold conductorHarmonicFactor
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro m hm
        exact B10MainGateBudget_support_mem_Icc hm
      · intro m hm hnot
        positivity

private theorem B10MainGateBudget_harmonicCube_le_logCube
    {N : ℕ} (hN : 2 ≤ N) :
    conductorHarmonicFactor N ^ 3 ≤ (1 + Real.log (N : ℝ)) ^ 3 := by
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hy : 0 ≤ 1 + Real.log (N : ℝ) := by
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
    linarith
  have hsquare :
      conductorHarmonicFactor N ^ 2 ≤ (1 + Real.log (N : ℝ)) ^ 2 := by
    exact (sq_le_sq₀ (conductorHarmonicFactor_nonneg N) hy).2
      (conductorHarmonicFactor_le N)
  calc
    conductorHarmonicFactor N ^ 3 =
        conductorHarmonicFactor N ^ 2 * conductorHarmonicFactor N := by
          ring
    _ ≤ (1 + Real.log (N : ℝ)) ^ 2 * conductorHarmonicFactor N := by
      exact mul_le_mul_of_nonneg_right hsquare (conductorHarmonicFactor_nonneg N)
    _ ≤ (1 + Real.log (N : ℝ)) ^ 2 * (1 + Real.log (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (conductorHarmonicFactor_le N) (by positivity)
    _ = (1 + Real.log (N : ℝ)) ^ 3 := by
      ring

/-- Finite reciprocal-totient budget for deleting the non-coprime part of the
actual `C10` main support. -/
theorem sum_gateLoss_le_logCube
    {N Q : ℕ} {b c T : ℝ} {w : ℕ → ℝ}
    (hQ : Q ≤ N) (hN : 2 ≤ N) (hb : 0 < b) (hT : 0 ≤ T)
    (hw : ∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → |w m| ≤ T / (m : ℝ)) :
    ∑ d ∈ Finset.Icc 1 Q, gateLoss N b c w d ≤
      (4 * T / b) * (1 + Real.log (N : ℝ)) ^ 3 := by
  let S := goldbachC10ProductSupport N b c
  calc
    ∑ d ∈ Finset.Icc 1 Q, gateLoss N b c w d
      ≤ ∑ d ∈ Finset.Icc 1 Q,
          ∑ m ∈ S, if ¬Nat.Coprime m d then ((d.totient : ℝ)⁻¹) * |w m| else 0 := by
          apply Finset.sum_le_sum
          intro d hd
          unfold gateLoss
          calc
            |((d.totient : ℝ)⁻¹) *
                ∑ m ∈ goldbachC10ProductSupport N b c with ¬Nat.Coprime m d, w m|
                = ((d.totient : ℝ)⁻¹) *
                    |∑ m ∈ goldbachC10ProductSupport N b c with ¬Nat.Coprime m d, w m| := by
                      rw [abs_mul, abs_of_nonneg]
                      positivity
            _ ≤ ((d.totient : ℝ)⁻¹) *
                ∑ m ∈ goldbachC10ProductSupport N b c with ¬Nat.Coprime m d, |w m| := by
                  gcongr
                  exact Finset.abs_sum_le_sum_abs _ _
            _ = ((d.totient : ℝ)⁻¹) *
                ∑ m ∈ goldbachC10ProductSupport N b c,
                  if ¬Nat.Coprime m d then |w m| else 0 := by
                    rw [← Finset.sum_filter]
            _ = ∑ m ∈ S, if ¬Nat.Coprime m d then ((d.totient : ℝ)⁻¹) * |w m| else 0 := by
                  subst S
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro m hm
                  split_ifs <;> simp
    _ = ∑ m ∈ S,
          ∑ d ∈ Finset.Icc 1 Q, if ¬Nat.Coprime m d then ((d.totient : ℝ)⁻¹) * |w m| else 0 := by
            exact Finset.sum_comm
    _ = ∑ m ∈ S,
          (∑ d ∈ Finset.Icc 1 Q, if ¬Nat.Coprime m d then ((d.totient : ℝ)⁻¹) else 0) *
            |w m| := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hrewrite :
                  (∑ d ∈ Finset.Icc 1 Q,
                      if ¬Nat.Coprime m d then ((d.totient : ℝ)⁻¹) * |w m| else 0) =
                    ∑ d ∈ Finset.Icc 1 Q,
                      (if ¬Nat.Coprime m d then ((d.totient : ℝ)⁻¹) else 0) * |w m| := by
                        refine Finset.sum_congr rfl ?_
                        intro d hd
                        split_ifs <;> ring
              rw [hrewrite, Finset.sum_mul]
    _ ≤ ∑ m ∈ S, ((4 / b) * conductorHarmonicFactor N ^ 2) * |w m| := by
          apply Finset.sum_le_sum
          intro m hm
          apply mul_le_mul_of_nonneg_right
          · subst S
            exact B10MainGateBudget_bad_inverseTotientMass_le hQ hb hm
          · exact abs_nonneg _
    _ = ((4 / b) * conductorHarmonicFactor N ^ 2) *
          ∑ m ∈ S, |w m| := by
            symm
            rw [Finset.mul_sum]
    _ ≤ ((4 / b) * conductorHarmonicFactor N ^ 2) *
          (T * conductorHarmonicFactor N) := by
            apply mul_le_mul_of_nonneg_left ?_ (by positivity)
            subst S
            exact B10MainGateBudget_weightMass_le hT hw
    _ = (4 * T / b) * conductorHarmonicFactor N ^ 3 := by
      ring
    _ ≤ (4 * T / b) * (1 + Real.log (N : ℝ)) ^ 3 := by
      apply mul_le_mul_of_nonneg_left
        (B10MainGateBudget_harmonicCube_le_logCube hN)
      positivity

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig