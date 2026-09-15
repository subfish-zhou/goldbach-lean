import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFiniteErrorPayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleClosedQuadrature
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitTupleGeometry

namespace Wu2008DoubleSieve.LowerTripleGroupedFinite
open Finset Real HighNonunitLegal LiLiuPrereqBuchstab
open scoped Classical

theorem tupleCubeEmbedding_coordinate {R : ℝ} (S : Finset PrimeTriple)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes R)
    (t : S) (j : Fin 3) :
    gridCoordinates R (tupleCubeEmbedding S hmem t) j =
      log (tupleCoordinates t.val j : ℝ) / log R := rfl

theorem tupleCubeEmbedding_log_sum {R : ℝ} (hR : 1 < R)
    (S : Finset PrimeTriple)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes R) (t : S) :
    (∑ j, gridCoordinates R (tupleCubeEmbedding S hmem t) j) =
      log ((tupleList t.val).prod : ℝ) / log R := by
  simp only [tupleCubeEmbedding_coordinate, ← sum_div]
  congr 1
  rw [← tupleCoordinates_product t.val, log_prod]
  intro j _
  have hh := hmem t.val t.property (tupleCoordinates t.val j) (by
    have hj : j.val < (tupleList t.val).length := by rw [tupleList_length]; exact j.isLt
    simp only [tupleCoordinates, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj)
  have hp := ((mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mp hh).1
  exact_mod_cast hp.ne_zero

theorem tuple_log_sub {N d : ℕ} {t : PrimeTriple} (hN : 0 < N) (hd : 0 < d)
    (ht : 0 < (tupleList t).prod) :
    log ((N : ℝ) / d) - log ((tupleList t).prod : ℝ) =
      log ((N : ℝ) / tupleProduct d t) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have ht' : ((tupleList t).prod : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  simp only [tupleProduct_literal, Nat.cast_mul, log_div hn hd',
    log_div hn (mul_ne_zero hd' ht'), log_mul hd' ht']
  ring

/-- The actual phi is retained; legality is supplied by the full three-dimensional cube. -/
theorem tupleCubeEmbedding_kernel {N d : ℕ} {δ : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hR : 1 < (N : ℝ)^(1/2-δ)/d)
    (hphi : 2 ≤ omega3XPhi N d δ)
    (S : Finset PrimeTriple)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N : ℝ)^(1/2-δ)/d))
    (t : S) (hprod : 0 < (tupleList t.val).prod) (hq : 1 < t.val.2.1) :
    buchstab (log ((N : ℝ)/tupleProduct d t.val) / log t.val.2.1) *
      ((N : ℝ)/tupleProduct d t.val) / log t.val.2.1 =
      ((N : ℝ)/(d*log ((N : ℝ)^(1/2-δ)/d))) *
        primeSlabWeight _ (tupleCubeEmbedding S hmem t) *
          LowerTripleContinuous.G (omega3XPhi N d δ)
            (gridCoordinates _ (tupleCubeEmbedding S hmem t)) := by
  let R := (N : ℝ)^(1/2-δ)/d
  let x := gridCoordinates R (tupleCubeEmbedding S hmem t)
  have hlogR : 0 < log R := log_pos hR
  have hlogq : 0 < log (t.val.2.1 : ℝ) := log_pos (by exact_mod_cast hq)
  have hx : x 1 = log (t.val.2.1 : ℝ) / log R := rfl
  have hsum := tupleCubeEmbedding_log_sum hR S hmem t
  have hsub := tuple_log_sub hN hd hprod
  have harg : (omega3XPhi N d δ - ∑ i, x i) / x 1 =
      log ((N : ℝ)/tupleProduct d t.val) / log t.val.2.1 := by
    rw [hx, hsum]
    unfold omega3XPhi
    rw [← sub_div, hsub, div_div_div_cancel_right₀ hlogR.ne']
  have hl : x ∈ legal 1 (omega3XPhi N d δ) := LowerTripleContinuous.cube_legal hphi (gridCoordinates_mem hR
    (tupleCubeEmbedding S hmem t))
  change _ = ((N : ℝ)/(d*log R)) * _ * G 1 (omega3XPhi N d δ) x
  rw [G_of_legal hl, harg, hx, tupleCubeEmbedding_weight]
  simp only [tupleProduct_literal, Nat.cast_mul]
  field_simp

/-- The original shifted lower bound alone is not used to close the r face.
The extra rLo inequality is an explicit, indispensable argument. -/
theorem tuple_embedding_closed_domain {N d : ℕ} {δ : ℝ} {p : SecondFunctionalParameters}
    (hR : 1 < (N : ℝ)^(1/2-δ)/d)
    (S : Finset PrimeTriple)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N : ℝ)^(1/2-δ)/d))
    (t : S) (j : Fin 6) (ht : t.val ∈ actualPrimeTriples N δ p j d)
    (hrlo : (LowerTripleGrouped.actualBands N δ p j d).2.2.2.2.1 ≤ (t.val.2.2 : ℝ)) :
    gridCoordinates _ (tupleCubeEmbedding S hmem t) ∈
      LowerTripleContinuous.D (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) j := by
  let R := (N : ℝ)^(1/2-δ)/d
  let L := fun q : ℕ => log (q : ℝ)/log R
  obtain ⟨hp,hq,_,hpq,hpre,hr,hl,hu⟩ := mem_primeTriples.mp ht
  have hp0 := (mem_primeWindow.mp hp).1.pos
  have hq0 := (mem_primeWindow.mp hq).1.pos
  have h01 : L t.val.1 ≤ L t.val.2.1 :=
    div_le_div_of_nonneg_right (log_le_log (by exact_mod_cast hp0)
      (by exact_mod_cast hpq.le)) (log_pos hR).le
  have h12 : L t.val.2.1 ≤ L t.val.2.2 :=
    div_le_div_of_nonneg_right (log_le_log (by exact_mod_cast hq0)
      ((le_max_left _ _).trans hl.le)) (log_pos hR).le
  have lower (q : ℕ) (a : ℝ) (h : wuLocalCutoff N δ d a ≤ (q : ℝ)) : 1/a ≤ L q :=
    HighNonunit.log_coordinate_lower hR h
  have upper (q : ℕ) (a : ℝ) (hq' : 0 < q)
      (h : (q : ℝ) ≤ wuLocalCutoff N δ d a) : L q ≤ 1/a :=
    HighNonunit.log_coordinate_upper hR hq' h
  change LowerTripleGrouped.actualPre N δ p j d t.val.1 t.val.2.1 at hpre
  revert hu
  revert hrlo
  revert hpre
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun i => Fin.elim0 i)))))) j
  all_goals
    intro hpre hrlo hu
    simp only [LowerTripleGrouped.actualPre, LowerTripleGrouped.actualBands,
      LowerTripleGrouped.bands, Matrix.cons_val_zero, Matrix.cons_val_succ] at hpre hrlo hu
    rcases hpre with ⟨hpl,hpu,hql,hqu⟩
    change _ ≤ L t.val.1 ∧ L t.val.1 ≤ _ ∧ _ ≤ L t.val.2.1 ∧ L t.val.2.1 ≤ _ ∧
      _ ≤ L t.val.2.2 ∧ L t.val.2.2 ≤ _ ∧ L t.val.1 ≤ L t.val.2.1 ∧ L t.val.2.1 ≤ L t.val.2.2
    exact ⟨lower _ _ hpl, upper _ _ hp0 hpu.le, lower _ _ hql,
      upper _ _ hq0 hqu.le, lower _ _ hrlo, upper _ _ hr.pos hu, h01, h12⟩

end Wu2008DoubleSieve.LowerTripleGroupedFinite
