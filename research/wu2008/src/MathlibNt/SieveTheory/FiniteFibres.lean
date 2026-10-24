import Mathlib.Algebra.BigOperators.Ring.Finset

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

/-- Sum the sizes of the output fibres satisfying `P`, retaining multiplicities.
The cardinalities may be cast into any additive commutative monoid with one. -/
theorem sum_card_fibres_filter_image {α β R : Type*} [DecidableEq β]
    [AddCommMonoidWithOne R]
    (A : Finset α) (out : α → β) (P : β → Prop) [DecidablePred P] :
    (∑ n ∈ (A.image out).filter P, ((A.filter (fun x => out x = n)).card : R)) =
      ((A.filter (fun x => P (out x))).card : R) := by
  simpa using sum_fibres_filter_image A out P (fun _ => (1 : R))

end MathlibNt.SieveTheory
