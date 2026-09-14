import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace MathlibNt.SieveTheory

/-- Push a labelled finite sum through an output predicate, retaining every fibre weight. -/
theorem sum_fibres_filter_image {α β M : Type*} [DecidableEq β] [AddCommMonoid M]
    (A : Finset α) (out : α → β) (P : β → Prop) [DecidablePred P] (w : α → M) :
    (∑ n ∈ (A.image out).filter P, ∑ x ∈ A.filter (fun x => out x = n), w x) =
      ∑ x ∈ A.filter (fun x => P (out x)), w x := by
  have hfilter : A.filter (fun x => out x ∈ (A.image out).filter P) =
      A.filter (fun x => P (out x)) := by
    apply Finset.filter_congr
    intro x hx
    simp [Finset.mem_image_of_mem out hx]
  simpa only [hfilter] using
    Finset.sum_fiberwise_eq_sum_filter A ((A.image out).filter P) out w

end MathlibNt.SieveTheory
