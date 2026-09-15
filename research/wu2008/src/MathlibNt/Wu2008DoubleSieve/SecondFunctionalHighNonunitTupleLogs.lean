import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSourceKMasses

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real HighNonunitLegal LiLiuPrereqBuchstab
open scoped Classical

theorem tupleCubeEmbedding_coordinate {m : ℕ} {R : ℝ} (S : Finset PrimeTuple)
    (hlen : ∀ t ∈ S, (tupleList t).length = m)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes R)
    (t : S) (j : Fin m) :
    gridCoordinates R (tupleCubeEmbedding S hlen hmem t) j =
      log (tupleCoordinates m t.val j : ℝ) / log R := rfl

theorem tuple_penultimate {m : ℕ} {t : PrimeTuple}
    (hlen : (tupleList t).length = m + 2) :
    tupleCoordinates (m + 2) t ⟨m, by omega⟩ = t.2.1 := by
  have hpre : t.1.length = m := by
    simp only [tupleList, List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  simp [tupleCoordinates, tupleList, hpre]

theorem tupleCubeEmbedding_log_sum {m : ℕ} {R : ℝ} (hR : 1 < R)
    (S : Finset PrimeTuple) (hlen : ∀ t ∈ S, (tupleList t).length = m)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes R) (t : S) :
    (∑ j, gridCoordinates R (tupleCubeEmbedding S hlen hmem t) j) =
      log ((tupleList t.val).prod : ℝ) / log R := by
  simp only [tupleCubeEmbedding_coordinate, ← sum_div]
  congr 1
  rw [← tupleCoordinates_product (hlen _ t.property), log_prod]
  intro j _
  have hh := hmem t.val t.property (tupleCoordinates m t.val j) (by
    have hj : j.val < (tupleList t.val).length := by rw [hlen _ t.property]; exact j.isLt
    simp only [tupleCoordinates, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj)
  have hp := ((mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mp hh).1
  exact_mod_cast hp.ne_zero

theorem tuple_log_sub {N d : ℕ} {t : PrimeTuple} (hN : 0 < N) (hd : 0 < d)
    (ht : 0 < (tupleList t).prod) :
    log ((N : ℝ) / d) - log ((tupleList t).prod : ℝ) =
      log ((N : ℝ) / tupleProduct d t) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have ht' : ((tupleList t).prod : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  simp only [tupleProduct, Nat.cast_mul, log_div hn hd',
    log_div hn (mul_ne_zero hd' ht'), log_mul hd' ht']
  ring

theorem tupleCubeEmbedding_legal_kernel {m N d : ℕ} {δ : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hR : 1 < (N : ℝ)^(1/2-δ)/d)
    (S : Finset PrimeTuple) (hlen : ∀ t ∈ S, (tupleList t).length = m + 2)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N : ℝ)^(1/2-δ)/d))
    (t : S) (hprod : 0 < (tupleList t.val).prod) (hp : 1 < t.val.2.1)
    (hgate : tupleProduct d t.val * t.val.2.1 ≤ N) :
    let R := (N : ℝ)^(1/2-δ)/d
    let x := gridCoordinates R (tupleCubeEmbedding S hlen hmem t)
    let j : Fin (m+2) := ⟨m, by omega⟩
    x ∈ legal j (omega3XPhi N d δ) ∧
    (omega3XPhi N d δ - ∑ i, x i) / x j =
      log ((N : ℝ)/tupleProduct d t.val) / log t.val.2.1 ∧
    buchstab (log ((N : ℝ)/tupleProduct d t.val) / log t.val.2.1) *
      ((N : ℝ)/tupleProduct d t.val) / log t.val.2.1 =
      ((N : ℝ)/d/log R) * primeSlabWeight R (tupleCubeEmbedding S hlen hmem t) *
        G j (omega3XPhi N d δ) x := by
  dsimp only
  let R := (N : ℝ)^(1/2-δ)/d
  let x := gridCoordinates R (tupleCubeEmbedding S hlen hmem t)
  let j : Fin (m+2) := ⟨m, by omega⟩
  have hlogR : 0 < log R := log_pos hR
  have hlogp : 0 < log (t.val.2.1 : ℝ) := log_pos (by exact_mod_cast hp)
  have hx : x j = log (t.val.2.1 : ℝ) / log R := by
    exact congrArg (fun q : ℕ => log (q : ℝ) / log R) (tuple_penultimate (hlen _ t.property))
  have hsum := tupleCubeEmbedding_log_sum hR S hlen hmem t
  have hsub := tuple_log_sub hN hd hprod
  have harg : (omega3XPhi N d δ - ∑ i, x i) / x j =
      log ((N : ℝ)/tupleProduct d t.val) / log t.val.2.1 := by
    rw [hx, hsum]
    unfold omega3XPhi
    rw [← sub_div, hsub, div_div_div_cancel_right₀ hlogR.ne']
  have hD : 0 < tupleProduct d t.val := Nat.mul_pos hd hprod
  have hl := log_le_log (by exact_mod_cast (lt_trans Nat.zero_lt_one hp) :
    (0 : ℝ) < t.val.2.1) ((legal_gate_iff N d t.val hD).mp hgate)
  have hlegal : x ∈ legal j (omega3XPhi N d δ) := by
    change (∑ i, x i) + x j ≤ _
    rw [hx, hsum]
    unfold omega3XPhi
    change log ((tupleList t.val).prod : ℝ) / log R + log (t.val.2.1 : ℝ) / log R ≤ _
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right hlogR).mpr
    rw [← hsub] at hl
    linarith
  refine ⟨hlegal, harg, ?_⟩
  rw [G_of_legal hlegal, harg, hx, tupleCubeEmbedding_weight]
  simp only [tupleProduct, Nat.cast_mul]
  change _ = ((N : ℝ)/d/log R) * (1/((tupleList t.val).prod : ℝ)) *
    (buchstab (log ((N : ℝ)/(d * ((tupleList t.val).prod : ℝ))) / log t.val.2.1) /
      (log (t.val.2.1 : ℝ)/log R))
  field_simp

end Wu2008DoubleSieve.HighNonunit
