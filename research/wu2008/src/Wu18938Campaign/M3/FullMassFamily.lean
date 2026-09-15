import WR2Gamma5FullMass

noncomputable section

namespace Wu18938Campaign.M3

open Finset Set Real Filter MeasureTheory Wu2008DoubleSieve
open Wu2008DoubleSieve.MotherPair WuPaper.R2Gamma5
open scoped Classical Topology Interval

structure FullCell (p : SecondFunctionalParameters) where
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  bounds : FullRectangle p A B C D
  separated : B ≤ C

def FullCell.region {p : SecondFunctionalParameters} (r : FullCell p) : Set (ℝ × ℝ) :=
  Ico r.A r.B ×ˢ Ico r.C r.D

def FullCell.sample {p : SecondFunctionalParameters} (r : FullCell p) : ℝ :=
  p.S * (1 - r.A - r.C)

theorem full_cells_disjoint {p : SecondFunctionalParameters} {r s : FullCell p}
    (hrs : Disjoint r.region s.region)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    Disjoint
      (rectLabels N δ (convolutionWuWindows N Δ V) r.A r.B r.C r.D)
      (rectLabels N δ (convolutionWuWindows N Δ V) s.A s.B s.C s.D) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' :
      (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1,
        gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ∈ r.region :=
    rectangle_coordinates hN hδ hδhi hb hx
  exact Set.disjoint_left.mp hrs hx' (rectangle_coordinates hN hδ hδhi hb hy)

theorem fullHMass_family_lower {p : SecondFunctionalParameters} (hp : FullParameters p)
    (F : Finset (FullCell p))
    (hF : (F : Set (FullCell p)).Pairwise (fun r s => Disjoint r.region s.region))
    (k : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        ((∑ r ∈ F, wuImprovementLimit true δ r.sample *
            rectIntegral r.A r.B r.C r.D) - ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
          fullHMass p N δ (convolutionWuWindows N Δ V)
            (termLabels p .gammaFive N δ (convolutionWuWindows N Δ V)) := by
  let η : ℝ := ε / ((F.card : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨T, hT4, hT⟩ := fullHMass_rectangle_producer p hp k hδ hδhi hη
  refine ⟨T, hT4, ?_⟩
  intro N hNT i Δ V hb
  have hN2 : 2 ≤ N := by omega
  have hδhalf : δ < 1 / 2 := by linarith
  let W := convolutionWuWindows N Δ V
  let X := fun r : FullCell p => rectLabels N δ W r.A r.B r.C r.D
  have hd : ∀ r ∈ F, ∀ s ∈ F, r ≠ s → Disjoint (X r) (X s) := by
    intro r hr s hs hrs
    exact full_cells_disjoint (hF hr hs hrs) hN2 hδ hδhalf hb
  have hs : F.biUnion X ⊆ termLabels p .gammaFive N δ W := by
    intro x hx
    obtain ⟨r, _, hrx⟩ := mem_biUnion.mp hx
    exact full_rectangle_subset hN2 hδ hδhalf hb r.bounds hrx
  have heq : (∑ r ∈ F, fullHMass p N δ W (X r)) =
      fullHMass p N δ W (F.biUnion X) := by
    unfold fullHMass
    rw [← mul_sum, sum_biUnion hd]
  have hsum := sum_le_sum (fun r (_hr : r ∈ F) =>
    hT N hNT i Δ V hb r.A r.B r.C r.D r.bounds)
  change (∑ r ∈ F, (wuImprovementLimit true δ r.sample *
    rectIntegral r.A r.B r.C r.D - η) *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W) ≤
        ∑ r ∈ F, fullHMass p N δ W (X r) at hsum
  rw [← sum_mul, sum_sub_distrib, sum_const, nsmul_eq_mul, heq] at hsum
  have hmono := fullHMass_mono hp hN2 hδ hδhalf hb hs (Finset.Subset.refl _)
  have hθ := gamma5Mass_theta_nonneg hN2 hδ hδhalf hb
  have hpay : (F.card : ℝ) * η ≤ ε := by
    have he : ((F.card : ℝ) + 1) * η = ε := by
      dsimp [η]
      exact mul_div_cancel₀ _ (by positivity)
    nlinarith
  exact (mul_le_mul_of_nonneg_right (by linarith : _ - ε ≤
    (∑ r ∈ F, wuImprovementLimit true δ r.sample * rectIntegral r.A r.B r.C r.D) -
      (F.card : ℝ) * η) hθ).trans (hsum.trans hmono)

end Wu18938Campaign.M3
