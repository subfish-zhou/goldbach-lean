import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFSieve

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


theorem linked_small_test (N : ℕ) (ε Z : ℝ) :
    goldbachG12LinkedSmallOutputMass N ε Z =
      ∑ x ∈ goldbachG12LinkedAtoms N ε,
        if N-x.2*x.1 < Nat.ceil Z then goldbachG12NormalizedCoefficient N x.1 else 0 := by
  let A := goldbachG12LinkedAtoms N ε
  let out := goldbachG12LinkedOutput N
  have hf := MathlibNt.SieveTheory.sum_fibres_filter_image A out (fun n => n < Nat.ceil Z)
    (fun x => goldbachG12NormalizedCoefficient N x.1)
  calc
    _ = ∑ x ∈ A.filter (fun x => out x < Nat.ceil Z),
        goldbachG12NormalizedCoefficient N x.1 := hf
    _ = _ := by
      rw [sum_filter]
      rfl


end G12RectangleWF
