import SigmaSimpleResidueAlgebra

noncomputable section
namespace SigmaSimpleResiduePrimitive
open Polynomial Complex Set
open scoped BigOperators

theorem eval_complex_map (P : ℝ[X]) (t : ℝ) :
    (P.map Complex.ofRealHom).eval (t : ℂ) = ((P.eval t : ℝ) : ℂ) := by
  exact Polynomial.eval_map_apply (p := P) Complex.ofRealHom t

theorem complex_eval_product (B : ℂ[X]) (hB : B.Separable) (t : ℂ) :
    B.eval t = B.leadingCoeff * ∏ z ∈ B.roots.toFinset, (t-z) := by
  classical
  rw [(IsAlgClosed.splits B).eval_eq_prod_roots]
  congr 1
  simp only [Finset.prod, Multiset.toFinset_val, (nodup_roots hB).dedup]

theorem simple_fraction (R B : ℝ[X]) (hB : B.Separable)
    (hR : R.degree < B.degree) (t : ℝ) (ht : B.eval t ≠ 0) :
    ((R.eval t / B.eval t : ℝ) : ℂ) =
      ∑ z ∈ (B.map Complex.ofRealHom).roots.toFinset, residue R B z / ((t : ℂ)-z) := by
  classical
  let Q := B.map Complex.ofRealHom
  have hQ : Q.Separable := hB.map
  have hQt : Q.eval (t : ℂ) ≠ 0 := by
    rw [eval_complex_map]
    exact Complex.ofReal_ne_zero.mpr ht
  have hprod := complex_eval_product Q hQ (t : ℂ)
  have havoid : ∀ z ∈ Q.roots.toFinset, (t : ℂ)-z ≠ 0 := by
    intro z hz he
    have hr := (mem_roots hQ.ne_zero).mp (Multiset.mem_toFinset.mp hz)
    apply hQt
    rw [sub_eq_zero.mp he]
    exact hr
  have hc : Q.roots.toFinset.card = B.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hQ),
      ← (IsAlgClosed.splits Q).natDegree_eq_card_roots]
    exact natDegree_map _
  have hd : (R.map Complex.ofRealHom).degree < Q.roots.toFinset.card := by
    rw [degree_map, hc, ← degree_eq_natDegree hB.ne_zero]
    exact hR
  have hf := lagrange_fraction Q.roots.toFinset (R.map Complex.ofRealHom) hd (t : ℂ) havoid
  rw [Complex.ofReal_div, ← eval_complex_map R, ← eval_complex_map B]
  change (R.map Complex.ofRealHom).eval (t : ℂ) / Q.eval (t : ℂ) = _
  rw [hprod, mul_comm Q.leadingCoeff, div_mul_eq_div_div, hf, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  dsimp [residue, Q]
  ring

end SigmaSimpleResiduePrimitive
