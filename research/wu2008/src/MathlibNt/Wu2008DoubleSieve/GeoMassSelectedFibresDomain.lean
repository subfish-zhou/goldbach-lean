import MathlibNt.Wu2008DoubleSieve.GeoMassSelectedFibresCoordinates

namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.SelectedFibres
open Set MeasureTheory
open scoped BigOperators
open SecondFunctionalJointTail

private theorem monotone_append_iff {m n : ℕ} (l : Fin m → ℝ) (r : Fin n → ℝ) :
    Monotone (Fin.append l r) ↔ Monotone l ∧ Monotone r ∧ ∀ i j, l i ≤ r j := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      simpa using h (show Fin.castAdd n i ≤ Fin.castAdd n j from hij)
    · intro i j hij
      simpa using h (show Fin.natAdd m i ≤ Fin.natAdd m j by simpa using hij)
    · intro i j
      have hij : Fin.castAdd n i ≤ Fin.natAdd m j := by
        simp only [Fin.le_def, Fin.val_castAdd, Fin.val_natAdd]
        omega
      simpa using h hij
  · rintro ⟨hl,hr,hcross⟩ i j hij
    revert j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · intro hij
        simpa using hl hij
      · intro _
        simpa using hcross i j
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · intro hij
        have := j.isLt
        simp only [Fin.le_def, Fin.val_castAdd, Fin.val_natAdd] at hij
        omega
      · intro hij
        have hij' : i ≤ j := by simpa using hij
        simpa using hr hij'

private theorem monotone_cons_iff {k : ℕ} (t : ℝ) (r : Fin k → ℝ) :
    Monotone (Fin.cons t r) ↔ Monotone r ∧ ∀ i, t ≤ r i := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simpa using h (show i.succ ≤ j.succ by simpa using hij)
    · simpa using h (Fin.zero_le i.succ)
  · rintro ⟨hr,ht⟩ i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact le_rfl
      | succ j => simpa using ht j
    | succ i =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j => simpa using hr (Fin.succ_le_succ_iff.mp hij)

theorem coordinates_domain (m k : ℕ) (a b : ℝ)
    (p : ℝ × (Fin m → ℝ) × (Fin k → ℝ)) :
    coordinates m k p ∈ orderedDomain (m + (k+1)) a b ↔
      p.1 ∈ Icc a b ∧ p.2.1 ∈ orderedDomain m a p.1 ∧
      p.2.2 ∈ orderedDomain k p.1 b := by
  rcases p with ⟨t,l,r⟩
  simp only [coordinates_apply, orderedDomain, mem_ofPred_eq, Fin.forall_fin_add,
    Fin.forall_fin_succ, Fin.append_left, Fin.append_right, Fin.cons_zero, Fin.cons_succ,
    monotone_append_iff, monotone_cons_iff]
  constructor
  · rintro ⟨⟨hlb,htb,hrb⟩,hl,⟨hr,htr⟩,hlr⟩
    refine ⟨htb, ⟨fun i => ⟨(hlb i).1, ?_⟩,hl⟩, ⟨fun i => ⟨htr i,(hrb i).2⟩,hr⟩⟩
    exact (hlr i).1
  · rintro ⟨htb,⟨hlb,hl⟩,⟨hrb,hr⟩⟩
    refine ⟨⟨fun i => ⟨(hlb i).1,(hlb i).2.trans htb.2⟩, htb,
      fun i => ⟨htb.1.trans (hrb i).1,(hrb i).2⟩⟩,
      hl, ⟨hr,fun i => (hrb i).1⟩, ?_⟩
    intro i
    exact ⟨(hlb i).2,fun j => (hlb i).2.trans (hrb j).1⟩

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.SelectedFibres
