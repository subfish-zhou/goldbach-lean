import MathlibNt.SieveTheory.LiLiuGoldbachErrorFoundations

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachEndpointBound (P : Prop) : Decidable P :=
  Classical.propDecidable P

private noncomputable def goldbachB6EndpointCarrier (N : ℕ) (z y : ℝ) : Finset ℕ :=
  (goldbachClosedPrimes N z y).filter (fun t : ℕ => y ≤ (t : ℝ))

private theorem goldbachB6EndpointCarrier_cast_eq
    {N t : ℕ} {z y : ℝ}
    (ht : t ∈ goldbachB6EndpointCarrier N z y) :
    (t : ℝ) = y := by
  rcases Finset.mem_filter.mp ht with ⟨htClosed, hyt⟩
  rcases mem_goldbachClosedPrimes_iff.mp htClosed with ⟨_, _, _, hty⟩
  exact le_antisymm hty hyt

private theorem goldbachB6EndpointCarrier_subsingleton
    {N u v : ℕ} {z y : ℝ}
    (hu : u ∈ goldbachB6EndpointCarrier N z y)
    (hv : v ∈ goldbachB6EndpointCarrier N z y) :
    u = v := by
  have huv : (u : ℝ) = (v : ℝ) := by
    calc
      (u : ℝ) = y := goldbachB6EndpointCarrier_cast_eq hu
      _ = (v : ℝ) := (goldbachB6EndpointCarrier_cast_eq hv).symm
  exact_mod_cast huv

private theorem goldbachClosedPrimes_eq_filter_ge
    (N : ℕ) (z : ℝ) {r t : ℕ}
    (hr : r ∈ goldbachClosedPrimes N z (t : ℝ)) :
    goldbachClosedPrimes N (r : ℝ) (t : ℝ) =
      (goldbachClosedPrimes N z (t : ℝ)).filter (fun s : ℕ => r ≤ s) := by
  ext s
  constructor
  · intro hs
    rcases mem_goldbachClosedPrimes_iff.mp hr with ⟨_, _, hrz, _⟩
    rcases mem_goldbachClosedPrimes_iff.mp hs with ⟨hsPrime, hsN, hrs, hst⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨mem_goldbachClosedPrimes_iff.mpr ?_, ?_⟩
    · exact ⟨hsPrime, hsN, hrz.trans hrs, hst⟩
    · exact_mod_cast hrs
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨hsClosed, hrs⟩
    rcases mem_goldbachClosedPrimes_iff.mp hsClosed with ⟨hsPrime, hsN, _, hst⟩
    exact mem_goldbachClosedPrimes_iff.mpr
      ⟨hsPrime, hsN, by exact_mod_cast hrs, hst⟩

private theorem left_dvd_of_triple_dvd
    {a b c n : ℕ}
    (h : a * b * c ∣ n) :
    a ∣ n := by
  have ha : a ∣ a * b * c := by
    simp [mul_assoc]
  exact dvd_trans ha h

private theorem middle_dvd_of_triple_dvd
    {a b c n : ℕ}
    (h : a * b * c ∣ n) :
    b ∣ n := by
  exact dvd_trans
    (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        dvd_mul_of_dvd_left (dvd_refl b) (a * c))
    h

private theorem right_dvd_of_triple_dvd
    {a b c n : ℕ}
    (h : a * b * c ∣ n) :
    c ∣ n := by
  exact dvd_trans
    (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        dvd_mul_of_dvd_left (dvd_refl c) (a * b))
    h

private theorem goldbachB6_slice_le_four_hundred_mul_card
    (A : Finset ℕ) (N t : ℕ) {κ z : ℝ}
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N)
    (hk : (1 : ℝ) / 21 < κ)
    (hz : z = (N : ℝ) ^ κ) :
    (∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
        ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
          literalH A (N * r) (r * s * t) s) ≤
      400 * ((A.filter fun n => t ∣ n).card : ℤ) := by
  let T := goldbachClosedPrimes N z (t : ℝ)
  have hsquare :
      (∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
          ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
            literalH A (N * r) (r * s * t) s) ≤
        ∑ r ∈ T,
          ∑ s ∈ T,
            literalH A (N * r) (r * s * t) s := by
    calc
      (∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
          ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
            literalH A (N * r) (r * s * t) s) =
        ∑ r ∈ T,
          ∑ s ∈ T.filter (fun s : ℕ => r ≤ s),
            literalH A (N * r) (r * s * t) s := by
              apply Finset.sum_congr rfl
              intro r hr
              simp [T, goldbachClosedPrimes_eq_filter_ge N z hr]
      _ ≤ ∑ r ∈ T,
            ∑ s ∈ T,
              literalH A (N * r) (r * s * t) s := by
            apply Finset.sum_le_sum
            intro r hr
            have hsplit :=
              Finset.sum_filter_add_sum_filter_not
                T
                (fun s : ℕ => r ≤ s)
                (fun s => literalH A (N * r) (r * s * t) s)
            have hnonneg :
                0 ≤ ∑ s ∈ T.filter (fun s : ℕ => ¬r ≤ s),
                  literalH A (N * r) (r * s * t) s := by
              refine Finset.sum_nonneg ?_
              intro s hs
              exact literalH_nonneg A (N * r) (r * s * t) s
            linarith
  let D := fun n : ℕ => T.filter (fun p : ℕ => p ∣ n)
  have hpointwise :
      ∀ n ∈ A,
        (∑ r ∈ T,
            ∑ s ∈ T,
              if literalHPoint (N * r) (r * s * t) s n then (1 : ℤ) else 0) ≤
          if t ∣ n then (400 : ℤ) else 0 := by
    intro n hnA
    by_cases htn : t ∣ n
    · have hDsubset :
          D n ⊆ largePrimeDivisors n z := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpT, hpdvd⟩
        rcases mem_goldbachClosedPrimes_iff.mp hpT with ⟨hpPrime, _, hpz, _⟩
        have hn0 : n ≠ 0 := by
          exact ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hA n hnA).1)
        simp [largePrimeDivisors, Nat.mem_primeFactors, hpPrime, hpdvd, hn0, hpz]
      have hDle :
          (D n).card ≤ (largePrimeDivisors n z).card :=
        Finset.card_le_card hDsubset
      have hDtwenty :
          (D n).card ≤ 20 := by
        have hLtwenty : (largePrimeDivisors n z).card ≤ 20 := by
          rw [hz]
          exact largePrimeDivisors_card_le_twenty (hA n hnA).1 (hA n hnA).2 hk
        exact le_trans hDle hLtwenty
      have hinner :
          ∀ r ∈ T,
            (∑ s ∈ T,
                if literalHPoint (N * r) (r * s * t) s n then (1 : ℤ) else 0) ≤
              if r ∣ n then ((D n).card : ℤ) else 0 := by
        intro r hr
        by_cases hrd : r ∣ n
        ·
          have hle :
              (∑ s ∈ T,
                  if literalHPoint (N * r) (r * s * t) s n then (1 : ℤ) else 0) ≤
                ∑ s ∈ T, (if s ∣ n then (1 : ℤ) else 0) := by
            apply Finset.sum_le_sum
            intro s hs
            by_cases hP : literalHPoint (N * r) (r * s * t) s n
            · have hsd : s ∣ n := middle_dvd_of_triple_dvd hP.1
              simp [hP, hsd]
            · by_cases hsd : s ∣ n <;> simp [hP, hsd]
          have hcard :
              (∑ s ∈ T, (if s ∣ n then (1 : ℤ) else 0)) = ((D n).card : ℤ) := by
            have hcard0 :
                (∑ s ∈ T, (if s ∣ n then (1 : ℤ) else 0)) =
                  (((T.filter fun s : ℕ => s ∣ n).card) : ℤ) := by
              exact Finset.sum_boole (fun s : ℕ => s ∣ n) T
            exact hcard0
          have hbound :
              (∑ s ∈ T,
                  if literalHPoint (N * r) (r * s * t) s n then (1 : ℤ) else 0) ≤
                ((D n).card : ℤ) := by
            exact hle.trans (le_of_eq hcard)
          simp [hrd] at hbound ⊢
          exact hbound
        ·
          have hzero :
              (∑ s ∈ T,
                  if literalHPoint (N * r) (r * s * t) s n then (1 : ℤ) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro s hs
            by_cases hP : literalHPoint (N * r) (r * s * t) s n
            · exfalso
              exact hrd (left_dvd_of_triple_dvd hP.1)
            · simp [hP]
          simp [hrd, hzero]
      have houter :
          (∑ r ∈ T,
              ∑ s ∈ T,
                if literalHPoint (N * r) (r * s * t) s n then (1 : ℤ) else 0) ≤
            ∑ r ∈ T, (if r ∣ n then ((D n).card : ℤ) else 0) := by
        apply Finset.sum_le_sum
        intro r hr
        exact hinner r hr
      have hcount :
          (∑ r ∈ T, (if r ∣ n then ((D n).card : ℤ) else 0)) =
            ((D n).card : ℤ) * ((D n).card : ℤ) := by
        have hcount1 :
            (∑ r ∈ T, (if r ∣ n then (1 : ℤ) else 0)) = ((D n).card : ℤ) := by
          have hcount10 :
              (∑ r ∈ T, (if r ∣ n then (1 : ℤ) else 0)) =
                (((T.filter fun r : ℕ => r ∣ n).card) : ℤ) := by
            exact Finset.sum_boole (fun r : ℕ => r ∣ n) T
          exact hcount10
        calc
          (∑ r ∈ T, (if r ∣ n then ((D n).card : ℤ) else 0)) =
              ∑ r ∈ T, ((if r ∣ n then (1 : ℤ) else 0) * ((D n).card : ℤ)) := by
                apply Finset.sum_congr rfl
                intro r hr
                by_cases hrd : r ∣ n <;> simp [hrd]
          _ = (∑ r ∈ T, (if r ∣ n then (1 : ℤ) else 0)) * ((D n).card : ℤ) := by
                rw [Finset.sum_mul]
          _ = ((D n).card : ℤ) * ((D n).card : ℤ) := by
                rw [hcount1]
      have hquad :
          ((D n).card : ℤ) * ((D n).card : ℤ) ≤ 400 := by
        have hDtwentyZ : ((D n).card : ℤ) ≤ 20 := by exact_mod_cast hDtwenty
        have hDnonneg : 0 ≤ ((D n).card : ℤ) := by exact_mod_cast Nat.zero_le (D n).card
        nlinarith
      have hbound :
          (∑ r ∈ T,
              ∑ s ∈ T,
                if literalHPoint (N * r) (r * s * t) s n then (1 : ℤ) else 0) ≤
            (400 : ℤ) := by
        calc
          (∑ r ∈ T,
              ∑ s ∈ T,
                if literalHPoint (N * r) (r * s * t) s n then (1 : ℤ) else 0) ≤
              ∑ r ∈ T, (if r ∣ n then ((D n).card : ℤ) else 0) := houter
          _ = ((D n).card : ℤ) * ((D n).card : ℤ) := hcount
          _ ≤ 400 := hquad
      simpa [htn] using hbound
    · have hzero :
          (∑ r ∈ T,
              ∑ s ∈ T,
                if literalHPoint (N * r) (r * s * t) s n then (1 : ℤ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        apply Finset.sum_eq_zero
        intro s hs
        by_cases hP : literalHPoint (N * r) (r * s * t) s n
        · exfalso
          exact htn (right_dvd_of_triple_dvd hP.1)
        · simp [hP]
      rw [hzero]
      simp [htn]
  calc
    (∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
        ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
          literalH A (N * r) (r * s * t) s) ≤
      ∑ r ∈ T,
        ∑ s ∈ T,
          literalH A (N * r) (r * s * t) s := hsquare
    _ =
      ∑ r ∈ T,
        ∑ s ∈ T,
          ∑ n ∈ A,
            if literalHPoint (N * r) (r * s * t) s n then (1 : ℤ) else 0 := by
          simp_rw [literalH_eq_sum_indicator]
    _ =
      ∑ r ∈ T,
        ∑ n ∈ A,
          ∑ s ∈ T,
            if literalHPoint (N * r) (r * s * t) s n then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.sum_comm]
    _ =
      ∑ n ∈ A,
        ∑ r ∈ T,
          ∑ s ∈ T,
            if literalHPoint (N * r) (r * s * t) s n then (1 : ℤ) else 0 := by
          rw [Finset.sum_comm]
    _ ≤ ∑ n ∈ A, (if t ∣ n then (400 : ℤ) else 0) := by
          apply Finset.sum_le_sum
          intro n hn
          exact hpointwise n hn
    _ = 400 * ((A.filter fun n => t ∣ n).card : ℤ) := by
          have hsum1 :
              (∑ n ∈ A, (if t ∣ n then (1 : ℤ) else 0)) =
                ((A.filter fun n : ℕ => t ∣ n).card : ℤ) := by
            exact Finset.sum_boole (fun n : ℕ => t ∣ n) A
          calc
            (∑ n ∈ A, (if t ∣ n then (400 : ℤ) else 0)) =
                ∑ n ∈ A, ((if t ∣ n then (1 : ℤ) else 0) * 400) := by
                  apply Finset.sum_congr rfl
                  intro n hn
                  by_cases htn : t ∣ n <;> simp [htn]
            _ = (∑ n ∈ A, (if t ∣ n then (1 : ℤ) else 0)) * 400 := by
                  rw [Finset.sum_mul]
            _ = 400 * ((A.filter fun n => t ∣ n).card : ℤ) := by
                  rw [hsum1]
                  ring

theorem goldbachB6_le_four_hundred_mul_div_y
    (A : Finset ℕ) (N : ℕ) {κ z y : ℝ}
    (hN : 1 ≤ N)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N)
    (hk : (1 : ℝ) / 21 < κ)
    (hz : z = (N : ℝ) ^ κ)
    (hzy : z ≤ y) :
    (goldbachB6 A N z y : ℝ) ≤ 400 * (N : ℝ) / y := by
  have hk0 : 0 < κ := by nlinarith
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hz0 : 0 < z := by
    rw [hz]
    exact Real.rpow_pos_of_pos hN0 _
  have hy0 : 0 < y := lt_of_lt_of_le hz0 hzy
  let U := goldbachB6EndpointCarrier N z y
  have houter_unique :
      ∀ {u v : ℕ}, u ∈ U → v ∈ U → u = v := by
    intro u v hu hv
    exact goldbachB6EndpointCarrier_subsingleton hu hv
  by_cases hU : U = ∅
  · calc
      (goldbachB6 A N z y : ℝ) = 0 := by
        change ((∑ t ∈ U,
            ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
              ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
                literalH A (N * r) (r * s * t) s : ℤ) : ℝ) = 0
        simp [U, hU]
      _ ≤ 400 * (N : ℝ) / y := by positivity
  · obtain ⟨t, htU⟩ : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
    have hUeq : U = {t} := by
      ext u
      constructor
      · intro hu
        exact Finset.mem_singleton.mpr (houter_unique hu htU)
      · intro hu
        rcases Finset.mem_singleton.mp hu with rfl
        exact htU
    rcases Finset.mem_filter.mp htU with ⟨htClosed, hyt⟩
    rcases mem_goldbachClosedPrimes_iff.mp htClosed with ⟨htPrime, _, _, hty⟩
    have htyEq : (t : ℝ) = y := le_antisymm hty hyt
    have htpos : 0 < t := htPrime.pos
    have hslice :
        ((∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
            ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
              literalH A (N * r) (r * s * t) s : ℤ) : ℝ) ≤
          400 * ((A.filter fun n => t ∣ n).card : ℝ) := by
      exact_mod_cast goldbachB6_slice_le_four_hundred_mul_card A N t hA hk hz
    have hcount :
        ((A.filter fun n => t ∣ n).card : ℝ) ≤ (N : ℝ) / t := by
      exact card_filter_dvd_le_div_real A N t
        (fun n hn => ⟨(hA n hn).1, (hA n hn).2.le⟩)
        htpos
    calc
      (goldbachB6 A N z y : ℝ) =
          ((∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
              ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
                literalH A (N * r) (r * s * t) s : ℤ) : ℝ) := by
            change ((∑ u ∈ U,
                ∑ r ∈ goldbachClosedPrimes N z (u : ℝ),
                  ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (u : ℝ),
                    literalH A (N * r) (r * s * u) s : ℤ) : ℝ) = _
            simp [U, hUeq]
      _ ≤ 400 * ((A.filter fun n => t ∣ n).card : ℝ) := hslice
      _ ≤ 400 * ((N : ℝ) / t) := by
            gcongr
      _ = 400 * (N : ℝ) / y := by
            rw [htyEq, div_eq_mul_inv, div_eq_mul_inv]
            ring

theorem goldbachB6_le_four_hundred_mul_div_z
    (A : Finset ℕ) (N : ℕ) {κ z y : ℝ}
    (hN : 1 ≤ N)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N)
    (hk : (1 : ℝ) / 21 < κ)
    (hz : z = (N : ℝ) ^ κ)
    (hzy : z ≤ y) :
    (goldbachB6 A N z y : ℝ) ≤ 400 * (N : ℝ) / z := by
  have hz0 : 0 < z := by
    have hN0 : 0 < (N : ℝ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
    rw [hz]
    exact Real.rpow_pos_of_pos hN0 _
  calc
    (goldbachB6 A N z y : ℝ) ≤ 400 * (N : ℝ) / y :=
      goldbachB6_le_four_hundred_mul_div_y A N hN hA hk hz hzy
    _ ≤ 400 * (N : ℝ) / z := by
      have hinv : 1 / y ≤ 1 / z := one_div_le_one_div_of_le hz0 hzy
      rw [div_eq_mul_inv, div_eq_mul_inv]
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hinv (show 0 ≤ 400 * (N : ℝ) by positivity)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig