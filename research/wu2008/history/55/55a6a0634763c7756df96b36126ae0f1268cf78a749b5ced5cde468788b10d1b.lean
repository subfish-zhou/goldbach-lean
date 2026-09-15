import MathlibNt.Wu2008DoubleSieve.Omega3CofactorSource

/-!
# Common finite layers of the actual cofactor labels

Enumerate each complete cofactor fibre, not its prime fibre. The enumeration
retains every d,p2,p1,n label, including labels with an empty prime interval.
Neither the enumeration nor its layer supports uses an arithmetic modulus.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

def omega3LayerFibre (L : Finset Omega3CofactorIndex) (e : ℕ) :
    Finset Omega3CofactorIndex :=
  L.filter fun c => omega3CofactorValue c = e

noncomputable def omega3LayerRank (L : Finset Omega3CofactorIndex) (e B : ℕ)
    (hB : (omega3LayerFibre L e).card ≤ B) :
    ↥(omega3LayerFibre L e) → Fin B :=
  fun c => Fin.castLE (by simpa only [Fintype.card_coe] using hB)
    (Fintype.equivFin ↥(omega3LayerFibre L e) c)

theorem omega3LayerRank_injective (L : Finset Omega3CofactorIndex) (e B : ℕ)
    (hB : (omega3LayerFibre L e).card ≤ B) :
    Function.Injective (omega3LayerRank L e B hB) := by
  intro a b hab
  apply (Fintype.equivFin ↥(omega3LayerFibre L e)).injective
  apply Fin.ext
  exact congrArg (fun x : Fin B => x.val) hab

noncomputable def omega3LayerSupport (L : Finset Omega3CofactorIndex) (j : ℕ) :
    Finset ℕ :=
  (L.image omega3CofactorValue).filter fun e => j < (omega3LayerFibre L e).card

noncomputable def omega3LayerLabel (L : Finset Omega3CofactorIndex) (j e : ℕ) :
    Omega3CofactorIndex :=
  if hj : j < (omega3LayerFibre L e).card then
    ((Fintype.equivFin ↥(omega3LayerFibre L e)).symm
      ⟨j, by simpa only [Fintype.card_coe] using hj⟩).val
  else ⟨0, 0, 0, 0⟩

theorem omega3LayerLabel_mem_fibre {L : Finset Omega3CofactorIndex} {j e : ℕ}
    (hj : j < (omega3LayerFibre L e).card) :
    omega3LayerLabel L j e ∈ omega3LayerFibre L e := by
  simp only [omega3LayerLabel, dif_pos hj]
  exact Subtype.property _

theorem omega3LayerLabel_mem {L : Finset Omega3CofactorIndex} {j e : ℕ}
    (he : e ∈ omega3LayerSupport L j) :
    omega3LayerLabel L j e ∈ L ∧ omega3CofactorValue (omega3LayerLabel L j e) = e :=
  mem_filter.mp (omega3LayerLabel_mem_fibre (mem_filter.mp he).2)

theorem omega3LayerLabel_rank {L : Finset Omega3CofactorIndex} {e B : ℕ}
    (hB : (omega3LayerFibre L e).card ≤ B) (c : ↥(omega3LayerFibre L e)) :
    omega3LayerLabel L (omega3LayerRank L e B hB c).val e = c.val := by
  have hc : (omega3LayerRank L e B hB c).val < (omega3LayerFibre L e).card := by
    simpa only [omega3LayerRank, Fin.val_castLE, Fintype.card_coe] using
      (Fintype.equivFin ↥(omega3LayerFibre L e) c).isLt
  rw [omega3LayerLabel, dif_pos hc]
  change ((Fintype.equivFin ↥(omega3LayerFibre L e)).symm
    (Fintype.equivFin ↥(omega3LayerFibre L e) c)).val = c.val
  exact congrArg Subtype.val
    ((Fintype.equivFin ↥(omega3LayerFibre L e)).symm_apply_apply c)

/-- Exact fibre enumeration, padded by zero up to the common layer bound. -/
theorem omega3Layer_fibre_sum (L : Finset Omega3CofactorIndex) (e B : ℕ)
    (hB : (omega3LayerFibre L e).card ≤ B) (F : Omega3CofactorIndex → ℝ) :
    (∑ c ∈ omega3LayerFibre L e, F c) =
      ∑ j ∈ range B, if j < (omega3LayerFibre L e).card
        then F (omega3LayerLabel L j e) else 0 := by
  rw [← sum_filter]
  rw [← sum_attach]
  apply sum_bij (fun c _ => (omega3LayerRank L e B hB c).val)
  · intro c _
    exact mem_filter.mpr ⟨mem_range.mpr (omega3LayerRank L e B hB c).isLt, by
      simpa only [omega3LayerRank, Fin.val_castLE, Fintype.card_coe] using
        (Fintype.equivFin ↥(omega3LayerFibre L e) c).isLt⟩
  · intro a _ b _ hab
    exact omega3LayerRank_injective L e B hB (Fin.ext hab)
  · intro j hj
    obtain ⟨_, hj⟩ := mem_filter.mp hj
    refine ⟨(Fintype.equivFin ↥(omega3LayerFibre L e)).symm
      ⟨j, by simpa only [Fintype.card_coe] using hj⟩, mem_attach _ _, ?_⟩
    simp only [omega3LayerRank, Equiv.apply_symm_apply, Fin.val_castLE]
  · intro c _
    rw [omega3LayerLabel_rank]

/-- One common finite partition gives equality for every test simultaneously.
In particular an AP modulus may occur in F, but not in any layer choice. -/
theorem omega3Layer_sum (L : Finset Omega3CofactorIndex) (B : ℕ)
    (hB : ∀ e, (omega3LayerFibre L e).card ≤ B) (F : Omega3CofactorIndex → ℝ) :
    (∑ c ∈ L, F c) =
      ∑ j ∈ range B, ∑ e ∈ omega3LayerSupport L j, F (omega3LayerLabel L j e) := by
  calc
    (∑ c ∈ L, F c) =
        ∑ e ∈ L.image omega3CofactorValue, ∑ c ∈ omega3LayerFibre L e, F c :=
      (sum_fiberwise_of_maps_to (fun _ hc => mem_image_of_mem _ hc) F).symm
    _ = ∑ e ∈ L.image omega3CofactorValue, ∑ j ∈ range B,
        if j < (omega3LayerFibre L e).card then F (omega3LayerLabel L j e) else 0 := by
      apply sum_congr rfl
      intro e _
      exact omega3Layer_fibre_sum L e B (hB e) F
    _ = _ := by
      rw [sum_comm]
      simp only [omega3LayerSupport, sum_filter]

end Wu2008DoubleSieve
