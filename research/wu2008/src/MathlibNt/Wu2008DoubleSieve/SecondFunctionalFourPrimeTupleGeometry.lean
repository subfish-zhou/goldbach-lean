import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeSourceKMasses
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteToClosedK

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset Real HighNonunitLegal LiLiuPrereqBuchstab
open scoped Classical

theorem tupleCubeEmbedding_coordinate {R : ℝ} (S : Finset PrimeTuple)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes R)
    (t : S) (j : Fin 4) :
    gridCoordinates R (tupleCubeEmbedding S hmem t) j =
      log (tupleCoordinates t.val j : ℝ) / log R := rfl

theorem tupleCubeEmbedding_log_sum {R : ℝ} (hR : 1 < R)
    (S : Finset PrimeTuple)
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

theorem tuple_log_sub {N d : ℕ} {t : PrimeTuple} (hN : 0 < N) (hd : 0 < d)
    (ht : 0 < (tupleList t).prod) :
    log ((N : ℝ) / d) - log ((tupleList t).prod : ℝ) =
      log ((N : ℝ) / tupleProduct d t) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have ht' : ((tupleList t).prod : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  simp only [tupleProduct_literal, Nat.cast_mul, log_div hn hd',
    log_div hn (mul_ne_zero hd' ht'), log_mul hd' ht']
  ring

theorem tupleCubeEmbedding_legal_kernel {N d : ℕ} {δ : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hR : 1 < (N : ℝ)^(1/2-δ)/d)
    (S : Finset PrimeTuple)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N : ℝ)^(1/2-δ)/d))
    (t : S) (hprod : 0 < (tupleList t.val).prod) (hp : 1 < t.val.1)
    (hgate : tupleProduct d t.val * t.val.1 ≤ N) :
    let R := (N : ℝ)^(1/2-δ)/d
    let x := gridCoordinates R (tupleCubeEmbedding S hmem t)
    let j : Fin 4 := 2
    x ∈ legal j (omega3XPhi N d δ) ∧
    (omega3XPhi N d δ - ∑ i, x i) / x j =
      log ((N : ℝ)/tupleProduct d t.val) / log t.val.1 ∧
    buchstab (log ((N : ℝ)/tupleProduct d t.val) / log t.val.1) *
      ((N : ℝ)/tupleProduct d t.val) / log t.val.1 =
      ((N : ℝ)/d/log R) * primeSlabWeight R (tupleCubeEmbedding S hmem t) *
        G j (omega3XPhi N d δ) x := by
  dsimp only
  let R := (N : ℝ)^(1/2-δ)/d
  let x := gridCoordinates R (tupleCubeEmbedding S hmem t)
  let j : Fin 4 := 2
  have hlogR : 0 < log R := log_pos hR
  have hlogp : 0 < log (t.val.1 : ℝ) := log_pos (by exact_mod_cast hp)
  have hx : x j = log (t.val.1 : ℝ) / log R := by
    rfl
  have hsum := tupleCubeEmbedding_log_sum hR S hmem t
  have hsub := tuple_log_sub hN hd hprod
  have harg : (omega3XPhi N d δ - ∑ i, x i) / x j =
      log ((N : ℝ)/tupleProduct d t.val) / log t.val.1 := by
    rw [hx, hsum]
    unfold omega3XPhi
    rw [← sub_div, hsub, div_div_div_cancel_right₀ hlogR.ne']
  have hD : 0 < tupleProduct d t.val := by
    rw [tupleProduct_literal]
    exact Nat.mul_pos hd hprod
  have hl := log_le_log (by exact_mod_cast (lt_trans Nat.zero_lt_one hp) :
    (0 : ℝ) < t.val.1) ((legal_gate_iff N d t.val hD).mp hgate)
  have hlegal : x ∈ legal j (omega3XPhi N d δ) := by
    change (∑ i, x i) + x j ≤ _
    rw [hx, hsum]
    unfold omega3XPhi
    change log ((tupleList t.val).prod : ℝ) / log R + log (t.val.1 : ℝ) / log R ≤ _
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right hlogR).mpr
    rw [← hsub] at hl
    linarith
  refine ⟨hlegal, harg, ?_⟩
  rw [G_of_legal hlegal, harg, hx, tupleCubeEmbedding_weight]
  simp only [tupleProduct_literal, Nat.cast_mul]
  change _ = ((N : ℝ)/d/log R) * (1/((tupleList t.val).prod : ℝ)) *
    (buchstab (log ((N : ℝ)/(d * ((tupleList t.val).prod : ℝ))) / log t.val.1) /
      (log (t.val.1 : ℝ)/log R))
  field_simp

/-- Actual reciprocal mother parameters inhabit the fixed compact parameter domain. -/
theorem mother_compact_parameters (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    FourPrimeContinuous.CompactParameters (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) := by
  have hs0 : 0 < p.s := lt_of_lt_of_le zero_lt_one hp.one_le_s
  have he : 0 < p.kappa3 := hs0.trans_le hp.s_le_kappa3
  have hc : 0 < p.kappa2 := he.trans hp.kappa3_lt_kappa2
  have hb : 0 < p.kappa1 := hc.trans hp.kappa2_lt_kappa1
  exact ⟨one_div_le_one_div_of_le hb (hp.kappa1_le_S.trans hp.S_le_ten),
    one_div_le_one_div_of_le hc hp.kappa2_lt_kappa1.le,
    one_div_le_one_div_of_le he hp.kappa3_lt_kappa2.le,
    one_div_le_one_div_of_le hs0 hp.s_le_kappa3,
    one_div_le_one_div_of_le (by norm_num) hs⟩

/-- The four literal closed domains, in the canonical word order. -/
def closedDomain (b c e f : ℝ) : Fin 4 → Set (Fin 4 → ℝ) :=
  Fin.cases (FourPrimeContinuous.D16 c e)
    (Fin.cases (FourPrimeContinuous.D17 c e f)
      (Fin.cases (FourPrimeContinuous.D18 c e f)
        (Fin.cases (FourPrimeContinuous.D19 b c e f) Fin.elim0)))

theorem colour_one {b c e : ℝ} {q : ℕ}
    (h : secondFunctionalMotherColour b c e q = 1) : b ≤ (q : ℝ) ∧ (q : ℝ) < c := by
  unfold secondFunctionalMotherColour at h
  split_ifs at h <;> first | omega | constructor <;> linarith

/-- Strict ordered prefix and original closed q band imply the literal closed mask. -/
theorem tuple_embedding_domain {N d : ℕ} {δ : ℝ} {p : SecondFunctionalParameters}
    (hp : p.MotherAdmissible) (hR : 1 < (N : ℝ)^(1/2-δ)/d)
    (S : Finset PrimeTuple)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N : ℝ)^(1/2-δ)/d))
    (t : S) (j : Fin 4) (ht : t.val ∈ actualPrimeTuples N δ p j d) :
    gridCoordinates _ (tupleCubeEmbedding S hmem t) ∈
      closedDomain (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) j := by
  let R := (N : ℝ)^(1/2-δ)/d
  let L := fun q : ℕ => log (q : ℝ)/log R
  obtain ⟨h3,h2,h1,_,hpre,hq⟩ := mem_primeTuples.mp ht
  have hpos1 := (mem_primeWindow.mp h1).1.pos
  have hpos2 := (mem_primeWindow.mp h2).1.pos
  have hpos3 := (mem_primeWindow.mp h3).1.pos
  have mono (q r : ℕ) (hq : 0 < q) (hqr : q ≤ r) : L q ≤ L r := by
    apply div_le_div_of_nonneg_right _ (log_pos hR).le
    exact log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqr)
  have h01 := mono _ _ hpos1 hpre.1.le
  have h12 := mono _ _ hpos2 hpre.2.1.le
  have h23 := mono _ _ hpos3 hq.2.1.le
  have two (q : ℕ) (hq0 : 0 < q)
      (hc : secondFunctionalMotherColour (wuLocalCutoff N δ d p.kappa1)
        (wuLocalCutoff N δ d p.kappa2) (wuLocalCutoff N δ d p.kappa3) q = 2) :
      1/p.kappa2 ≤ L q ∧ L q ≤ 1/p.kappa3 :=
    ⟨HighNonunit.log_coordinate_lower hR (HighUnitSource.colour_two hc).1,
      HighNonunit.log_coordinate_upper hR hq0 (HighUnitSource.colour_two hc).2.le⟩
  have three (q : ℕ)
      (hc : secondFunctionalMotherColour (wuLocalCutoff N δ d p.kappa1)
        (wuLocalCutoff N δ d p.kappa2) (wuLocalCutoff N δ d p.kappa3) q = 3) :
      1/p.kappa3 ≤ L q :=
    HighNonunit.log_coordinate_lower hR (HighUnitSource.colour_three hc)
  have hc := hpre.2.2
  have hlo := hq.2.2.1
  have hhi := hq.2.2.2
  revert hc hlo hhi
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))) j
  · intro hc hlo hhi
    change _ = [2,2,2] at hc
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc
    have hu : (t.val.2.2.2 : ℝ) ≤ wuLocalCutoff N δ d p.kappa3 := by
      simpa [lastUpper, FourPrimeUnit.word] using hhi
    exact ⟨(two _ hpos1 hc.1).1,h01,h12,h23,
      HighNonunit.log_coordinate_upper hR hq.1.pos hu⟩
  · intro hc hlo hhi
    change _ = [2,2,2] at hc
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc
    have hl : wuLocalCutoff N δ d p.kappa3 ≤ (t.val.2.2.2 : ℝ) := by
      simpa [lastLower, FourPrimeUnit.word] using hlo
    have hu : (t.val.2.2.2 : ℝ) ≤ wuLocalCutoff N δ d p.s := by
      simpa [lastUpper, FourPrimeUnit.word] using hhi
    exact ⟨(two _ hpos1 hc.1).1,h01,h12,(two _ hpos3 hc.2.2).2,
      HighNonunit.log_coordinate_lower hR hl,HighNonunit.log_coordinate_upper hR hq.1.pos hu⟩
  · intro hc hlo hhi
    change _ = [2,2,3] at hc
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc
    have hu : (t.val.2.2.2 : ℝ) ≤ wuLocalCutoff N δ d p.s := by
      simpa [lastUpper, FourPrimeUnit.word] using hhi
    exact ⟨(two _ hpos1 hc.1).1,h01,(two _ hpos2 hc.2.1).2,
      three _ hc.2.2,h23,HighNonunit.log_coordinate_upper hR hq.1.pos hu⟩
  · intro hc hlo hhi
    change _ = [1,3,3] at hc
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc
    have hcol := colour_one hc.1
    have hu : (t.val.2.2.2 : ℝ) ≤ wuLocalCutoff N δ d p.s := by
      simpa [lastUpper, FourPrimeUnit.word] using hhi
    have he : 0 < p.kappa3 := lt_of_lt_of_le zero_lt_one (hp.one_le_s.trans hp.s_le_kappa3)
    exact ⟨HighNonunit.log_coordinate_lower hR hcol.1,
      HighNonunit.log_coordinate_upper hR hpos1 hcol.2.le,
      one_div_le_one_div_of_le he hp.kappa3_lt_kappa2.le,
      three _ hc.2.1,h12,h23,HighNonunit.log_coordinate_upper hR hq.1.pos hu⟩

end Wu2008DoubleSieve.FourPrimeNonunit
