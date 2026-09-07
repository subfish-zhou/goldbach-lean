import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFOutput

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace G12RectangleWF

def linkedEmbed (p : ℕ × ℕ) : GoldbachG12LinkedAtom := ⟨p.1,p.2⟩

theorem linkedEmbed_injective : Function.Injective linkedEmbed := by
  intro p q h
  exact Prod.ext (congrArg Sigma.fst h)
    (congrArg (fun x : GoldbachG12LinkedAtom => x.2) h)

theorem rectangle_image_subset (N : ℕ) (ε : ℝ) (M T : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (2*T : ℕ) < (N : ℝ)^(1/10 : ℝ)) :
    (G12LowRectangle.rectangle N ε M T).image linkedEmbed ⊆ goldbachG12LinkedAtoms N ε := by
  intro x hx
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
  have hm := G12LowRectangle.rectangle_subset_mother N ε M T hlow hhigh hp
  have hd := (G12LowRectangle.mother_linked_iff N p.1 p.2 ε).mp hm
  exact mem_sigma.mpr ⟨hd.1,hd.2.1⟩

theorem linked_small_test (N : ℕ) (ε Z : ℝ) :
    goldbachG12LinkedSmallOutputMass N ε Z =
      ∑ x ∈ goldbachG12LinkedAtoms N ε,
        if N-x.2*x.1 < Nat.ceil Z then goldbachG12NormalizedCoefficient N x.1 else 0 := by
  let A := goldbachG12LinkedAtoms N ε
  let out := goldbachG12LinkedOutput N
  let U := (A.image out).filter (fun n => n < Nat.ceil Z)
  have hf := sum_fiberwise_eq_sum_filter A U out
    (fun x => goldbachG12NormalizedCoefficient N x.1)
  have he : A.filter (fun x => out x ∈ U) = A.filter (fun x => out x < Nat.ceil Z) := by
    ext x
    simp only [mem_filter]
    exact ⟨fun h => ⟨h.1,(mem_filter.mp h.2).2⟩,
      fun h => ⟨h.1,mem_filter.mpr ⟨mem_image.mpr ⟨x,h.1,rfl⟩,h.2⟩⟩⟩
  calc
    _ = ∑ x ∈ A.filter (fun x => out x ∈ U),
        goldbachG12NormalizedCoefficient N x.1 := hf
    _ = _ := by
      rw [he, sum_filter]
      rfl

/-- Inclusion in the actual global G12 mother supplies the established 20
per-output bound; the original multiplicity restores 8000, not 20. -/
theorem smallOutput_le (N : ℕ) (hN : 2 ≤ N) (ε Z : ℝ) (M T : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (2*T : ℕ) < (N : ℝ)^(1/10 : ℝ)) :
    smallOutput N ε Z M T ≤ 8000*(Nat.ceil Z : ℝ) := by
  have hm : (∑ p ∈ G12LowRectangle.rectangle N ε M T,
      if N-p.2*p.1 < Nat.ceil Z then goldbachG12NormalizedCoefficient N p.1 else 0) ≤
      goldbachG12LinkedSmallOutputMass N ε Z := by
    rw [linked_small_test]
    calc
      _ = ∑ x ∈ (G12LowRectangle.rectangle N ε M T).image linkedEmbed,
          if N-x.2*x.1 < Nat.ceil Z then goldbachG12NormalizedCoefficient N x.1 else 0 := by
        rw [sum_image]
        · rfl
        · exact fun _ _ _ _ h => linkedEmbed_injective h
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg
        (rectangle_image_subset N ε M T hlow hhigh)
        (fun x _ _ => by split_ifs; exact (goldbachG12NormalizedCoefficient_bounds N x.1).1; positivity)
  rw [smallOutput_eq_original]
  simp only [mul_ite, mul_one, mul_zero]
  have hb := goldbachG12LinkedSmallOutputMass_le hN ε Z
  linarith

end G12RectangleWF
