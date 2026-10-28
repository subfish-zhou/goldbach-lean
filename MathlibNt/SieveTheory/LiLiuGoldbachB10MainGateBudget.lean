import MathlibNt.SieveTheory.LiLiuGoldbachB10ProductCount
import MathlibNt.SieveTheory.FiniteCoprimeGateBudget

noncomputable section

open scoped BigOperators
open Classical Finset
open AnalyticNumberTheory.LargeSieve

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


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

/-- Finite reciprocal-totient budget for deleting the non-coprime part of the
actual `C10` main support. -/
theorem sum_gateLoss_le_logCube
    {N Q : ℕ} {b c T : ℝ} {w : ℕ → ℝ}
    (hQ : Q ≤ N) (hN : 2 ≤ N) (hb : 0 < b) (hT : 0 ≤ T)
    (hw : ∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → |w m| ≤ T / (m : ℝ)) :
    ∑ d ∈ Finset.Icc 1 Q, gateLoss N b c w d ≤
      (4 * T / b) * (1 + Real.log (N : ℝ)) ^ 3 := by
  have hfactor : ∀ m ∈ goldbachC10ProductSupport N b c,
      (∀ p ∈ m.primeFactors, b ≤ (p : ℝ)) ∧ m.primeFactors.card ≤ 2 := by
    intro m hm
    obtain ⟨rs, hrs, hprod⟩ := mem_goldbachC10ProductSupport_iff.mp hm
    obtain ⟨hr, hs, _, hbr, hrc, hcs, _⟩ := mem_goldbachC10Pairs_iff.mp hrs
    have hf : m.primeFactors = {rs.1, rs.2} := by
      rw [← hprod, goldbachC10Prod, Nat.primeFactors_mul hr.ne_zero hs.ne_zero,
        hr.primeFactors, hs.primeFactors, singleton_union]
    rw [hf]
    refine ⟨?_, (card_insert_le _ _).trans (by simp)⟩
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact hbr
    · exact (mem_singleton.mp hp) ▸ hbr.trans (hrc.trans hcs)
  simpa only [Nat.cast_ofNat, show (2 : ℝ) * 2 = 4 by norm_num,
    gateLoss, div_eq_mul_inv, mul_comm] using
    (G11FiniteGate.sum_gate_le_logCube (K := 2) hN hQ hb hT
      (fun _ hm => B10MainGateBudget_support_mem_Icc hm)
      (fun m hm => (hfactor m hm).1) (fun m hm => (hfactor m hm).2)
      (fun _ hm => hw hm))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig