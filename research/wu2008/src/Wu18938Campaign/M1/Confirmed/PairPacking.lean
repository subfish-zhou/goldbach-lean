import Wu18938Campaign.M1.Confirmed.PairIntegral
import Wu18938Campaign.M1.Confirmed.PairChildren
import MathlibNt.Wu2008DoubleSieve.MotherPairGainPacking

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Pair

open Wu2008DoubleSieve MotherPair Finset Real
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical

theorem term_mass_mono {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : AnalyticParameters p) (j : Term)
    {X Y : Finset Gamma5ClassicalLabel} (hXY : X ⊆ Y)
    (hY : Y ⊆ termLabels p j N δ (convolutionWuWindows N Δ V)) :
    gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X ≤
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) Y := by
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num)
      (MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl (by exact_mod_cast hN))
  unfold gamma5ClassicalMainMass
  apply mul_le_mul_of_nonneg_left _ hli
  apply sum_le_sum_of_subset_of_nonneg hXY
  intro x hx _
  have hg := geometry hb hN hη hδ (classical_cap hp) (term_cap hb hN hη hδ p hp j (hY hx))
  have hC := (wuSingularSeries_pos (gamma5ClassicalProduct x * N)
    (Nat.mul_pos hg.product_pos (by omega))).le
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)
    (mul_nonneg (Nat.cast_nonneg _) (log_pos hg.level_gt_one).le)

theorem packing_child_mass {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} {j : Term} (r : GainRectangle p j)
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ) :
    (∑ a ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.A r.B),
      ∑ b ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D),
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ
          (Fin.cons (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A a)
            (Fin.cons (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C b) V)))) =
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) (packing N δ Δ V r) := by
  simp_rw [child_theta]
  unfold gamma5ClassicalMainMass
  rw [packing_sum hR hΔ]
  simp only [mul_sum]

theorem packing_relative_mass (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ (j : Term) (r : GainRectangle p j),
      1 < gamma5GainScale N δ V → 1 < Δ →
      packing N δ Δ V r ⊆ termLabels p j N δ (convolutionWuWindows N Δ V) →
      (∑ a ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.A r.B),
        ∑ b ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D),
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ
            (Fin.cons (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A a)
              (Fin.cons (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C b) V)))) ≤
        (classicalIntegral p j + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := term_mass p hp m hη hδ he
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb j r hR hΔ hsub
  rw [packing_child_mass r hR hΔ]
  have hm := term_mass_mono hb (by omega) hη hδ p hp j hsub (Subset.refl _)
  have hnorm := (le_abs_self _).trans (hT N hN i Δ V hb j)
  nlinarith only [hm,hnorm]

end Wu18938Campaign.M1.Confirmed.Pair
