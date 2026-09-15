import MathlibNt.SieveTheory.LiLiuGoldbachErrorFoundations

open scoped BigOperators

open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachRepeatBound (P : Prop) : Decidable P :=
  Classical.propDecidable P

private abbrev RepeatTriple := Σ _t : ℕ, Σ _r : ℕ, ℕ

private def repeatTripleProd (a : RepeatTriple) : ℕ :=
  a.2.1 * a.2.2 * a.1

private noncomputable def goldbachRepeatShapes (N : ℕ) (z y : ℝ) : Finset RepeatTriple :=
  (goldbachHalfOpenPrimes N z y).sigma fun t =>
    (goldbachClosedPrimes N z (t : ℝ)).sigma fun r =>
      (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter (fun s : ℕ => r = s ∨ s = t)

private noncomputable def goldbachRepeatAtomsAt (n N : ℕ) (z y : ℝ) : Finset RepeatTriple :=
  (goldbachRepeatShapes N z y).filter (fun a : RepeatTriple => repeatTripleProd a ∣ n)

private noncomputable def goldbachSquareCarrierAt (n N : ℕ) (z : ℝ) : Finset ℕ :=
  (goldbachSquarePrimes N z).filter (fun q : ℕ => q ^ 2 ∣ n)

private def repeatEncode (a : RepeatTriple) : Σ _q : ℕ, ℕ :=
  if _hrs : a.2.1 = a.2.2 then ⟨a.2.1, a.1⟩ else ⟨a.2.2, a.2.1⟩

private def repeatDecode (qv : Σ _q : ℕ, ℕ) : RepeatTriple :=
  if _hqv : qv.1 ≤ qv.2 then ⟨qv.2, ⟨qv.1, qv.1⟩⟩ else ⟨qv.1, ⟨qv.2, qv.1⟩⟩

private theorem literalH_le_dvdFiberCard
    (A : Finset ℕ) (M d : ℕ) (x : ℝ) :
    literalH A M d x ≤ ((A.filter fun n => d ∣ n).card : ℤ) := by
  unfold literalH
  exact_mod_cast Finset.card_le_card
    (Finset.monotone_filter_right A (p := literalHPoint M d x)
      (q := fun n => d ∣ n) (fun _ _ hn => hn.1))

private theorem mem_goldbachRepeatShapes_iff {N : ℕ} {z y : ℝ} {a : RepeatTriple} :
    a ∈ goldbachRepeatShapes N z y ↔
      a.1 ∈ goldbachHalfOpenPrimes N z y ∧
      a.2.1 ∈ goldbachClosedPrimes N z (a.1 : ℝ) ∧
      a.2.2 ∈ goldbachClosedPrimes N (a.2.1 : ℝ) (a.1 : ℝ) ∧
      (a.2.1 = a.2.2 ∨ a.2.2 = a.1) := by
  simp [goldbachRepeatShapes]

private theorem mem_goldbachRepeatAtomsAt_iff {n N : ℕ} {z y : ℝ} {a : RepeatTriple} :
    a ∈ goldbachRepeatAtomsAt n N z y ↔
      a ∈ goldbachRepeatShapes N z y ∧ repeatTripleProd a ∣ n := by
  rw [goldbachRepeatAtomsAt, Finset.mem_filter]

private theorem sum_boole_eq_card_filter_int {α : Type*} [DecidableEq α]
    (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (∑ x ∈ s, if P x then (1 : ℤ) else 0) = ((s.filter P).card : ℤ) := by
  exact Finset.sum_boole P s

private theorem sum_repeatAtomsAt_eq_card
    (n N : ℕ) (z y : ℝ) :
    (∑ a ∈ goldbachRepeatShapes N z y, if repeatTripleProd a ∣ n then (1 : ℤ) else 0) =
      ((goldbachRepeatAtomsAt n N z y).card : ℤ) := by
  rw [goldbachRepeatAtomsAt]
  exact sum_boole_eq_card_filter_int (goldbachRepeatShapes N z y) (fun a => repeatTripleProd a ∣ n)

private theorem sum_squareCarrierAt_eq_card
    (n N : ℕ) (z : ℝ) :
    (∑ q ∈ goldbachSquarePrimes N z, if q ^ 2 ∣ n then (1 : ℤ) else 0) =
      ((goldbachSquareCarrierAt n N z).card : ℤ) := by
  rw [goldbachSquareCarrierAt]
  exact sum_boole_eq_card_filter_int (goldbachSquarePrimes N z) (fun q => q ^ 2 ∣ n)

private theorem goldbachR_le_sum_repeatAtomsAt_card
    (A : Finset ℕ) (N : ℕ) (z y : ℝ) :
    goldbachR A N z y ≤ ∑ n ∈ A, ((goldbachRepeatAtomsAt n N z y).card : ℤ) := by
  have hflat :
      (∑ a ∈ goldbachRepeatShapes N z y,
          ((A.filter fun n => repeatTripleProd a ∣ n).card : ℤ)) =
        ∑ t ∈ goldbachHalfOpenPrimes N z y,
          ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
            ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
                (fun s : ℕ => r = s ∨ s = t),
              ((A.filter fun n => r * s * t ∣ n).card : ℤ) := by
        unfold goldbachRepeatShapes
        simp_rw [Finset.sum_sigma']
        rfl
  calc
    goldbachR A N z y
        ≤ ∑ t ∈ goldbachHalfOpenPrimes N z y,
            ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
              ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
                  (fun s : ℕ => r = s ∨ s = t),
                ((A.filter fun n => r * s * t ∣ n).card : ℤ) := by
                  unfold goldbachR
                  refine Finset.sum_le_sum ?_
                  intro t ht
                  refine Finset.sum_le_sum ?_
                  intro r hr
                  refine Finset.sum_le_sum ?_
                  intro s hs
                  simpa using literalH_le_dvdFiberCard A (N * r) (r * s * t) s
    _ = ∑ a ∈ goldbachRepeatShapes N z y,
          ((A.filter fun n => repeatTripleProd a ∣ n).card : ℤ) := hflat.symm
    _ = ∑ a ∈ goldbachRepeatShapes N z y,
          ∑ n ∈ A, if repeatTripleProd a ∣ n then (1 : ℤ) else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            symm
            exact sum_boole_eq_card_filter_int A (fun n => repeatTripleProd a ∣ n)
    _ = ∑ n ∈ A, ∑ a ∈ goldbachRepeatShapes N z y, if repeatTripleProd a ∣ n then (1 : ℤ) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ n ∈ A, ((goldbachRepeatAtomsAt n N z y).card : ℤ) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact sum_repeatAtomsAt_eq_card n N z y

private theorem repeatEncode_mapsTo
    {n N : ℕ} {κ y : ℝ}
    (hn1 : 1 ≤ n) (hnN : n < N)
    (a : RepeatTriple) (ha : a ∈ goldbachRepeatAtomsAt n N ((N : ℝ) ^ κ) y) :
    repeatEncode a ∈
      (goldbachSquareCarrierAt n N ((N : ℝ) ^ κ)).sigma
        (fun _q => largePrimeDivisors n ((N : ℝ) ^ κ)) := by
  cases a with
  | mk t rs =>
    cases rs with
    | mk r s =>
      have hn0 : n ≠ 0 := by omega
      rcases mem_goldbachRepeatAtomsAt_iff.mp ha with ⟨hshape, hdiv⟩
      rcases mem_goldbachRepeatShapes_iff.mp hshape with ⟨ht, hr, hs, hrepeat⟩
      rcases mem_goldbachHalfOpenPrimes_iff.mp ht with ⟨htPrime, _, htz, _⟩
      rcases mem_goldbachClosedPrimes_iff.mp hr with ⟨hrPrime, _, hrz, hrt⟩
      rcases mem_goldbachClosedPrimes_iff.mp hs with ⟨hsPrime, _, hrs, _hst⟩
      by_cases hrsEq : r = s
      · subst s
        simp [repeatEncode]
        constructor
        · apply Finset.mem_filter.mpr
          refine ⟨mem_goldbachSquarePrimes_iff.mpr ?_, ?_⟩
          · refine ⟨hrPrime, hrz, ?_⟩
            have hrSqDvd : r ^ 2 ∣ n := by
              have hrSqDvdProd : r ^ 2 ∣ repeatTripleProd ⟨t, ⟨r, r⟩⟩ := by
                rw [pow_two]
                exact ⟨t, by simp [repeatTripleProd, mul_assoc]⟩
              exact dvd_trans hrSqDvdProd hdiv
            exact le_trans (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hn1) hrSqDvd) hnN.le
          · have hrSqDvd : r ^ 2 ∣ n := by
              have hrSqDvdProd : r ^ 2 ∣ repeatTripleProd ⟨t, ⟨r, r⟩⟩ := by
                rw [pow_two]
                exact ⟨t, by simp [repeatTripleProd, mul_assoc]⟩
              exact dvd_trans hrSqDvdProd hdiv
            exact hrSqDvd
        · apply Finset.mem_filter.mpr
          refine ⟨Nat.mem_primeFactors.mpr ?_, htz⟩
          refine ⟨htPrime, ?_, hn0⟩
          have htDvdProd : t ∣ repeatTripleProd ⟨t, ⟨r, r⟩⟩ := by
            exact ⟨r * r, by simp [repeatTripleProd, mul_comm]⟩
          exact dvd_trans htDvdProd hdiv
      · have hstEq : s = t := by
          rcases hrepeat with h | h
          · exact (hrsEq h).elim
          · exact h
        subst t
        simp [repeatEncode, hrsEq]
        constructor
        · apply Finset.mem_filter.mpr
          refine ⟨mem_goldbachSquarePrimes_iff.mpr ?_, ?_⟩
          · refine ⟨hsPrime, hrz.trans hrs, ?_⟩
            have hsSqDvd : s ^ 2 ∣ n := by
              have hsSqDvdProd : s ^ 2 ∣ repeatTripleProd ⟨s, ⟨r, s⟩⟩ := by
                rw [pow_two]
                exact ⟨r, by
                  simp [repeatTripleProd]
                  ring⟩
              exact dvd_trans hsSqDvdProd hdiv
            exact le_trans (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hn1) hsSqDvd) hnN.le
          · have hsSqDvd : s ^ 2 ∣ n := by
              have hsSqDvdProd : s ^ 2 ∣ repeatTripleProd ⟨s, ⟨r, s⟩⟩ := by
                rw [pow_two]
                exact ⟨r, by
                  simp [repeatTripleProd]
                  ring⟩
              exact dvd_trans hsSqDvdProd hdiv
            exact hsSqDvd
        · apply Finset.mem_filter.mpr
          refine ⟨Nat.mem_primeFactors.mpr ?_, hrz⟩
          refine ⟨hrPrime, ?_, hn0⟩
          have hrDvdProd : r ∣ repeatTripleProd ⟨s, ⟨r, s⟩⟩ := by
            exact ⟨s * s, by
              simp [repeatTripleProd]
              ring⟩
          exact dvd_trans hrDvdProd hdiv

private theorem repeatDecode_repeatEncode
    {n N : ℕ} {κ y : ℝ}
    {a : RepeatTriple}
    (ha : a ∈ goldbachRepeatAtomsAt n N ((N : ℝ) ^ κ) y) :
    repeatDecode (repeatEncode a) = a := by
  cases a with
  | mk t rs =>
    cases rs with
    | mk r s =>
      rcases mem_goldbachRepeatAtomsAt_iff.mp ha with ⟨hshape, _hdiv⟩
      rcases mem_goldbachRepeatShapes_iff.mp hshape with ⟨_ht, hr, hs, hrepeat⟩
      rcases mem_goldbachClosedPrimes_iff.mp hr with ⟨_hrPrime, _, _, hrt⟩
      rcases mem_goldbachClosedPrimes_iff.mp hs with ⟨_hsPrime, _, hrs, hst⟩
      have hrsNat : r ≤ s := by exact_mod_cast hrs
      have hstNat : s ≤ t := by exact_mod_cast hst
      have hrtNat : r ≤ t := by exact_mod_cast hrt
      by_cases hrsEq : r = s
      · subst s
        simp [repeatEncode, repeatDecode, hrtNat]
      · have hstEq : s = t := by
          rcases hrepeat with h | h
          · exact (hrsEq h).elim
          · exact h
        have hlt : r < s := lt_of_le_of_ne hrsNat hrsEq
        subst t
        simp [repeatEncode, repeatDecode, hrsEq, not_le_of_gt hlt]

private theorem repeatEncode_injOn
    {n N : ℕ} {κ y : ℝ} :
    Set.InjOn repeatEncode (goldbachRepeatAtomsAt n N ((N : ℝ) ^ κ) y) := by
  intro a ha b hb hab
  have hleft := congrArg repeatDecode hab
  simpa [repeatDecode_repeatEncode ha, repeatDecode_repeatEncode hb] using hleft

private theorem goldbachRepeatAtomsAt_card_le_twenty_mul_squareCarrier
    {n N : ℕ} {κ y : ℝ}
    (hn1 : 1 ≤ n) (hnN : n < N) (hk : (1 : ℝ) / 21 < κ) :
    ((goldbachRepeatAtomsAt n N ((N : ℝ) ^ κ) y).card : ℤ) ≤
      20 * ((goldbachSquareCarrierAt n N ((N : ℝ) ^ κ)).card : ℤ) := by
  have hcard :
      (goldbachRepeatAtomsAt n N ((N : ℝ) ^ κ) y).card ≤
        ((goldbachSquareCarrierAt n N ((N : ℝ) ^ κ)).sigma
          (fun q => largePrimeDivisors n ((N : ℝ) ^ κ))).card := by
    refine Finset.card_le_card_of_injOn repeatEncode ?_ repeatEncode_injOn
    intro a ha
    exact repeatEncode_mapsTo hn1 hnN a ha
  have hcap : (largePrimeDivisors n ((N : ℝ) ^ κ)).card ≤ 20 :=
    largePrimeDivisors_card_le_twenty hn1 hnN hk
  have hnat :
      (goldbachRepeatAtomsAt n N ((N : ℝ) ^ κ) y).card ≤
        (goldbachSquareCarrierAt n N ((N : ℝ) ^ κ)).card * 20 := by
    calc
      (goldbachRepeatAtomsAt n N ((N : ℝ) ^ κ) y).card
          ≤ ((goldbachSquareCarrierAt n N ((N : ℝ) ^ κ)).sigma
              (fun q => largePrimeDivisors n ((N : ℝ) ^ κ))).card := hcard
      _ = ∑ q ∈ goldbachSquareCarrierAt n N ((N : ℝ) ^ κ),
            (largePrimeDivisors n ((N : ℝ) ^ κ)).card := by
              rw [Finset.card_sigma]
      _ ≤ ∑ q ∈ goldbachSquareCarrierAt n N ((N : ℝ) ^ κ), 20 := by
            refine Finset.sum_le_sum ?_
            intro q hq
            exact hcap
      _ = (goldbachSquareCarrierAt n N ((N : ℝ) ^ κ)).card * 20 := by
            simp [mul_comm]
  simpa [mul_comm] using (show (((goldbachRepeatAtomsAt n N ((N : ℝ) ^ κ) y).card : ℕ) : ℤ) ≤
      (((goldbachSquareCarrierAt n N ((N : ℝ) ^ κ)).card * 20 : ℕ) : ℤ) by
        exact_mod_cast hnat)

private theorem sum_goldbachSquareCarrierAt_eq_goldbachQA
    (A : Finset ℕ) (N : ℕ) (z : ℝ) :
    (∑ n ∈ A, ((goldbachSquareCarrierAt n N z).card : ℤ)) = goldbachQA A N z := by
  calc
    (∑ n ∈ A, ((goldbachSquareCarrierAt n N z).card : ℤ))
        = ∑ n ∈ A, ∑ q ∈ goldbachSquarePrimes N z, if q ^ 2 ∣ n then (1 : ℤ) else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            exact (sum_squareCarrierAt_eq_card n N z).symm
    _ = ∑ q ∈ goldbachSquarePrimes N z, ∑ n ∈ A, if q ^ 2 ∣ n then (1 : ℤ) else 0 := by
          rw [Finset.sum_comm]
    _ = goldbachQA A N z := by
          unfold goldbachQA
          apply Finset.sum_congr rfl
          intro q hq
          exact sum_boole_eq_card_filter_int A (fun n => q ^ 2 ∣ n)

/-- The actual repeat mass is controlled by `20` copies of the actual square
mass `QA`, using the unique repeated-prime encoding from Li--Liu's proof. -/
theorem goldbachR_le_twenty_mul_goldbachQA
    (A : Finset ℕ) (N : ℕ) (κ y : ℝ)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N)
    (hk : (1 : ℝ) / 21 < κ) :
    goldbachR A N ((N : ℝ) ^ κ) y ≤ 20 * goldbachQA A N ((N : ℝ) ^ κ) := by
  calc
    goldbachR A N ((N : ℝ) ^ κ) y
        ≤ ∑ n ∈ A, ((goldbachRepeatAtomsAt n N ((N : ℝ) ^ κ) y).card : ℤ) :=
          goldbachR_le_sum_repeatAtomsAt_card A N ((N : ℝ) ^ κ) y
    _ ≤ ∑ n ∈ A, 20 * ((goldbachSquareCarrierAt n N ((N : ℝ) ^ κ)).card : ℤ) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          exact goldbachRepeatAtomsAt_card_le_twenty_mul_squareCarrier (hA n hn).1 (hA n hn).2 hk
    _ = 20 * ∑ n ∈ A, ((goldbachSquareCarrierAt n N ((N : ℝ) ^ κ)).card : ℤ) := by
          rw [← Finset.mul_sum]
    _ = 20 * goldbachQA A N ((N : ℝ) ^ κ) := by
          rw [sum_goldbachSquareCarrierAt_eq_goldbachQA]

/-- Combined with the already-proved square-tail estimate, the repeat mass is
bounded by `40 N / z` once `z = N^κ ≥ 2`. -/
theorem goldbachR_real_le_forty_mul_div
    (A : Finset ℕ) (N : ℕ) (κ y : ℝ)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N)
    (hk : (1 : ℝ) / 21 < κ)
    (hz : 2 ≤ (N : ℝ) ^ κ) :
    (goldbachR A N ((N : ℝ) ^ κ) y : ℝ) ≤ 40 * (N : ℝ) / ((N : ℝ) ^ κ) := by
  have hR : (goldbachR A N ((N : ℝ) ^ κ) y : ℝ) ≤ 20 * (goldbachQA A N ((N : ℝ) ^ κ) : ℝ) := by
    exact_mod_cast goldbachR_le_twenty_mul_goldbachQA A N κ y hA hk
  have hQA :
      (goldbachQA A N ((N : ℝ) ^ κ) : ℝ) ≤ 2 * (N : ℝ) / ((N : ℝ) ^ κ) :=
    goldbachQA_real_le_two_mul_div A N ((N : ℝ) ^ κ) hA hz
  calc
    (goldbachR A N ((N : ℝ) ^ κ) y : ℝ)
        ≤ 20 * (goldbachQA A N ((N : ℝ) ^ κ) : ℝ) := hR
    _ ≤ 20 * (2 * (N : ℝ) / ((N : ℝ) ^ κ)) := by gcongr
    _ = 40 * (N : ℝ) / ((N : ℝ) ^ κ) := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig