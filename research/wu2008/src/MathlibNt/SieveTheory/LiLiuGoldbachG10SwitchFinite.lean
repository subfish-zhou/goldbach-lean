import MathlibNt.SieveTheory.LiLiuGoldbachG10Cofactor
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped BigOperators
open Filter
open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachG10SwitchFinite (P : Prop) : Decidable P :=
  Classical.propDecidable P

private theorem one_twentyfirst_lt_of_parameter_window {β : ℝ}
    (hβ : (1 : ℝ) / 18 < β) : (1 : ℝ) / 21 < β := by
  nlinarith

private theorem sum_squarePrimeFiber_cards_eq_goldbachQA
    (A : Finset ℕ) (N : ℕ) (z : ℝ) :
    (∑ n ∈ A, (((goldbachSquarePrimes N z).filter fun q : ℕ => q ^ 2 ∣ n).card : ℤ)) =
      goldbachQA A N z := by
  calc
    (∑ n ∈ A, (((goldbachSquarePrimes N z).filter fun q : ℕ => q ^ 2 ∣ n).card : ℤ))
        = ∑ n ∈ A, ∑ q ∈ goldbachSquarePrimes N z, if q ^ 2 ∣ n then (1 : ℤ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            exact (Finset.sum_boole (p := fun q : ℕ => q ^ 2 ∣ n)
              (s := goldbachSquarePrimes N z) :
                (∑ q ∈ goldbachSquarePrimes N z, if q ^ 2 ∣ n then (1 : ℤ) else 0) =
                  (((goldbachSquarePrimes N z).filter fun q : ℕ => q ^ 2 ∣ n).card : ℤ)).symm
    _ = ∑ q ∈ goldbachSquarePrimes N z, ∑ n ∈ A, if q ^ 2 ∣ n then (1 : ℤ) else 0 := by
          rw [Finset.sum_comm]
    _ = goldbachQA A N z := by
          unfold goldbachQA
          refine Finset.sum_congr rfl ?_
          intro q hq
          exact (Finset.sum_boole (p := fun n : ℕ => q ^ 2 ∣ n) (s := A) :
            (∑ n ∈ A, if q ^ 2 ∣ n then (1 : ℤ) else 0) =
              ((A.filter fun n : ℕ => q ^ 2 ∣ n).card : ℤ))

private noncomputable def goldbachG10BadTarget
    (N : ℕ) (ε β : ℝ) : Finset (Σ _n : ℕ, ℕ × ℕ) :=
  ((goldbachDifferenceCarrier N ε).filter fun n => ¬Nat.Coprime n N).sigma fun n =>
    (largePrimeDivisors n ((N : ℝ) ^ β)).product (largePrimeDivisors n ((N : ℝ) ^ β))

theorem goldbachG10BadActualAtoms_le_four_hundred_badCount
    {N : ℕ} {ε β γ : ℝ}
    (hε : 0 < ε) (hβ : (1 : ℝ) / 21 < β) :
    ((goldbachG10BadActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).card : ℤ) ≤
      400 * goldbachBadCount (goldbachDifferenceCarrier N ε) N := by
  let f : (Σ _rs : ℕ × ℕ, ℕ) → (Σ n : ℕ, ℕ × ℕ) := fun x => ⟨x.2, x.1⟩
  have hmap :
      Set.MapsTo f
        (goldbachG10BadActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ))
        (goldbachG10BadTarget N ε β) := by
    intro x hx
    rcases mem_goldbachG10BadActualAtoms_iff.mp hx with ⟨hActual, hbad⟩
    have hnA := (mem_goldbachG10ActualAtoms_iff.mp hActual).2.1
    have hfst := goldbachG10ActualAtom_fst_mem_largePrimeDivisors (N := N) (ε := ε) (β := β)
      (γ := γ) hε (hx := hActual)
    have hsnd := goldbachG10ActualAtom_snd_mem_largePrimeDivisors (N := N) (ε := ε) (β := β)
      (γ := γ) hε (hx := hActual)
    exact by
      simp [f, goldbachG10BadTarget, hnA, hbad, hfst, hsnd]
  have hinj :
      Set.InjOn f (goldbachG10BadActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) := by
    intro x hx y hy hxy
    cases x
    cases y
    simp [f] at hxy ⊢
    exact ⟨hxy.2, hxy.1⟩
  calc
    ((goldbachG10BadActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).card : ℤ)
        ≤ ((goldbachG10BadTarget N ε β).card : ℤ) := by
            exact_mod_cast Finset.card_le_card_of_injOn f hmap hinj
    _ = ∑ n ∈ (goldbachDifferenceCarrier N ε).filter (fun n => ¬Nat.Coprime n N),
          (((largePrimeDivisors n ((N : ℝ) ^ β)).card : ℤ) *
            ((largePrimeDivisors n ((N : ℝ) ^ β)).card : ℤ)) := by
            simp [goldbachG10BadTarget, Finset.card_product, Nat.cast_mul]
    _ ≤ ∑ n ∈ (goldbachDifferenceCarrier N ε).filter (fun n => ¬Nat.Coprime n N), (400 : ℤ) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hbounds := goldbachG10DifferenceCarrier_bounds (N := N) (ε := ε) (n := n) hε
            ((Finset.mem_filter.mp hn).1)
          have hcard :
              (largePrimeDivisors n ((N : ℝ) ^ β)).card ≤ 20 :=
            largePrimeDivisors_card_le_twenty hbounds.1 hbounds.2.1 hβ
          have hcardZ : ((largePrimeDivisors n ((N : ℝ) ^ β)).card : ℤ) ≤ 20 := by
            exact_mod_cast hcard
          have hnonneg : 0 ≤ ((largePrimeDivisors n ((N : ℝ) ^ β)).card : ℤ) := by
            exact_mod_cast Nat.zero_le (largePrimeDivisors n ((N : ℝ) ^ β)).card
          nlinarith
    _ = 400 * goldbachBadCount (goldbachDifferenceCarrier N ε) N := by
          simp [goldbachBadCount, mul_comm]

private noncomputable def goldbachG10RSquareTarget
    (N : ℕ) (ε β : ℝ) : Finset (Σ _n : ℕ, ℕ × ℕ) :=
  (goldbachDifferenceCarrier N ε).sigma fun n =>
    (((goldbachSquarePrimes N ((N : ℝ) ^ β)).filter fun r : ℕ => r ^ 2 ∣ n).product
      (largePrimeDivisors n ((N : ℝ) ^ β)))

theorem goldbachG10RSquareActualAtoms_le_twenty_mul_goldbachQA
    {N : ℕ} {ε β γ : ℝ}
    (hε : 0 < ε) (hβ0 : (1 : ℝ) / 21 < β) :
    ((goldbachG10RSquareActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).card : ℤ) ≤
      20 * goldbachQA (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) := by
  let f : (Σ _rs : ℕ × ℕ, ℕ) → (Σ n : ℕ, ℕ × ℕ) := fun x => ⟨x.2, x.1⟩
  have hmap :
      Set.MapsTo f
        (goldbachG10RSquareActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ))
        (goldbachG10RSquareTarget N ε β) := by
    intro x hx
    rcases mem_goldbachG10RSquareActualAtoms_iff.mp hx with ⟨hActual, _, hrsq⟩
    have hnA := (mem_goldbachG10ActualAtoms_iff.mp hActual).2.1
    have hPair := mem_goldbachC10Pairs_iff.mp (mem_goldbachG10ActualAtoms_iff.mp hActual).1
    have hsnd := goldbachG10ActualAtom_snd_mem_largePrimeDivisors (N := N) (ε := ε) (β := β)
      (γ := γ) hε (hx := hActual)
    have hbounds := goldbachG10DifferenceCarrier_bounds (N := N) (ε := ε) (n := x.2) hε
      (mem_goldbachG10ActualAtoms_iff.mp hActual).2.1
    have hrsqLe : x.1.1 ^ 2 ≤ N := by
      have hle : x.1.1 ^ 2 ≤ x.2 := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hbounds.1) hrsq
      exact hle.trans hbounds.2.1.le
    exact by
      simp [f, goldbachG10RSquareTarget, hnA, mem_goldbachSquarePrimes_iff, hPair.1, hPair.2.2.2.1,
        hrsq, hrsqLe, hsnd]
  have hinj :
      Set.InjOn f (goldbachG10RSquareActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) := by
    intro x hx y hy hxy
    cases x
    cases y
    simp [f] at hxy ⊢
    exact ⟨hxy.2, hxy.1⟩
  calc
    ((goldbachG10RSquareActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).card : ℤ)
        ≤ ((goldbachG10RSquareTarget N ε β).card : ℤ) := by
            exact_mod_cast Finset.card_le_card_of_injOn f hmap hinj
    _ = ∑ n ∈ goldbachDifferenceCarrier N ε,
          (((((goldbachSquarePrimes N ((N : ℝ) ^ β)).filter fun r : ℕ => r ^ 2 ∣ n).card : ℤ)) *
            (((largePrimeDivisors n ((N : ℝ) ^ β)).card : ℤ))) := by
            simp [goldbachG10RSquareTarget, Finset.card_product, Nat.cast_mul]
    _ ≤ ∑ n ∈ goldbachDifferenceCarrier N ε,
          20 * (((goldbachSquarePrimes N ((N : ℝ) ^ β)).filter fun r : ℕ => r ^ 2 ∣ n).card : ℤ) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hbounds := goldbachG10DifferenceCarrier_bounds (N := N) (ε := ε) (n := n) hε hn
          have hlarge :
              (largePrimeDivisors n ((N : ℝ) ^ β)).card ≤ 20 :=
            largePrimeDivisors_card_le_twenty hbounds.1 hbounds.2.1 hβ0
          have hlargeZ : ((largePrimeDivisors n ((N : ℝ) ^ β)).card : ℤ) ≤ 20 := by
            exact_mod_cast hlarge
          have hsquareNonneg :
              0 ≤ (((goldbachSquarePrimes N ((N : ℝ) ^ β)).filter fun r : ℕ => r ^ 2 ∣ n).card : ℤ) := by
            exact_mod_cast Nat.zero_le
              ((goldbachSquarePrimes N ((N : ℝ) ^ β)).filter fun r : ℕ => r ^ 2 ∣ n).card
          nlinarith
    _ = 20 * goldbachQA (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) := by
          rw [← Finset.mul_sum]
          congr 1
          exact sum_squarePrimeFiber_cards_eq_goldbachQA (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β)

private noncomputable def goldbachG10SSquareTarget
    (N : ℕ) (ε β : ℝ) : Finset (Σ _n : ℕ, ℕ × ℕ) :=
  (goldbachDifferenceCarrier N ε).sigma fun n =>
    (((goldbachSquarePrimes N ((N : ℝ) ^ β)).filter fun s : ℕ => s ^ 2 ∣ n).product
      (largePrimeDivisors n ((N : ℝ) ^ β)))

theorem goldbachG10SSquareActualAtoms_le_twenty_mul_goldbachQA
    {N : ℕ} {ε β γ : ℝ}
    (hε : 0 < ε) (hβ0 : (1 : ℝ) / 21 < β) :
    ((goldbachG10SSquareActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).card : ℤ) ≤
      20 * goldbachQA (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) := by
  let f : (Σ _rs : ℕ × ℕ, ℕ) → (Σ n : ℕ, ℕ × ℕ) := fun x => ⟨x.2, (x.1.2, x.1.1)⟩
  have hmap :
      Set.MapsTo f
        (goldbachG10SSquareActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ))
        (goldbachG10SSquareTarget N ε β) := by
    intro x hx
    rcases mem_goldbachG10SSquareActualAtoms_iff.mp hx with ⟨hActual, _, _, hssq⟩
    have hnA := (mem_goldbachG10ActualAtoms_iff.mp hActual).2.1
    have hPair := mem_goldbachC10Pairs_iff.mp (mem_goldbachG10ActualAtoms_iff.mp hActual).1
    have hfst := goldbachG10ActualAtom_fst_mem_largePrimeDivisors (N := N) (ε := ε) (β := β)
      (γ := γ) hε (hx := hActual)
    have hbounds := goldbachG10DifferenceCarrier_bounds (N := N) (ε := ε) (n := x.2) hε
      (mem_goldbachG10ActualAtoms_iff.mp hActual).2.1
    have hssqLe : x.1.2 ^ 2 ≤ N := by
      have hle : x.1.2 ^ 2 ≤ x.2 := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hbounds.1) hssq
      exact hle.trans hbounds.2.1.le
    have hsLarge : (N : ℝ) ^ β ≤ (x.1.2 : ℝ) := by
      exact le_trans hPair.2.2.2.1 (le_trans hPair.2.2.2.2.1 hPair.2.2.2.2.2.1)
    exact by
      simp [f, goldbachG10SSquareTarget, hnA, mem_goldbachSquarePrimes_iff, hPair.2.1, hsLarge,
        hssq, hssqLe, hfst]
  have hinj :
      Set.InjOn f (goldbachG10SSquareActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) := by
    intro x hx y hy hxy
    cases x
    cases y
    simp [f] at hxy ⊢
    exact ⟨by exact Prod.ext hxy.2.2 hxy.2.1, hxy.1⟩
  calc
    ((goldbachG10SSquareActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).card : ℤ)
        ≤ ((goldbachG10SSquareTarget N ε β).card : ℤ) := by
            exact_mod_cast Finset.card_le_card_of_injOn f hmap hinj
    _ = ∑ n ∈ goldbachDifferenceCarrier N ε,
          (((((goldbachSquarePrimes N ((N : ℝ) ^ β)).filter fun s : ℕ => s ^ 2 ∣ n).card : ℤ)) *
            (((largePrimeDivisors n ((N : ℝ) ^ β)).card : ℤ))) := by
            simp [goldbachG10SSquareTarget, Finset.card_product, Nat.cast_mul]
    _ ≤ ∑ n ∈ goldbachDifferenceCarrier N ε,
          20 * (((goldbachSquarePrimes N ((N : ℝ) ^ β)).filter fun s : ℕ => s ^ 2 ∣ n).card : ℤ) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hbounds := goldbachG10DifferenceCarrier_bounds (N := N) (ε := ε) (n := n) hε hn
          have hlarge :
              (largePrimeDivisors n ((N : ℝ) ^ β)).card ≤ 20 :=
            largePrimeDivisors_card_le_twenty hbounds.1 hbounds.2.1 hβ0
          have hlargeZ : ((largePrimeDivisors n ((N : ℝ) ^ β)).card : ℤ) ≤ 20 := by
            exact_mod_cast hlarge
          have hsquareNonneg :
              0 ≤ (((goldbachSquarePrimes N ((N : ℝ) ^ β)).filter fun s : ℕ => s ^ 2 ∣ n).card : ℤ) := by
            exact_mod_cast Nat.zero_le
              ((goldbachSquarePrimes N ((N : ℝ) ^ β)).filter fun s : ℕ => s ^ 2 ∣ n).card
          nlinarith
    _ = 20 * goldbachQA (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) := by
          rw [← Finset.mul_sum]
          congr 1
          exact sum_squarePrimeFiber_cards_eq_goldbachQA (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β)

theorem goldbachG10Corrected_actual_le_pi10_with_errors
    {N : ℕ} {ε β γ : ℝ}
    (hε : 0 < ε)
    (hβ : (1 : ℝ) / 18 < β)
    (hβγ : β < (1 - 3 * β) / 3)
    (hγ : (1 - 3 * β) / 3 < γ)
    (hcut : 1 < ε * (N : ℝ) ^ ((1 : ℝ) / 6)) :
    goldbachG10Corrected (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) ≤
      goldbachPi10 N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) +
        400 * goldbachBadCount (goldbachDifferenceCarrier N ε) N +
        40 * goldbachQA (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) := by
  let T := goldbachG10ActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  let B := goldbachG10BadActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  let U := goldbachG10NonbadActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  let R := goldbachG10RSquareActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  let V := goldbachG10NoRSquareActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  let S := goldbachG10SSquareActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  let G := goldbachG10GoodActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  have hcardT :
      goldbachG10Corrected (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) =
        (T.card : ℤ) := by
    simpa [T, goldbachG10ActualAtoms] using goldbachG10Corrected_eq_card_atoms
      (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  have hsplit1 : (B.card : ℤ) + (U.card : ℤ) = (T.card : ℤ) := by
    simpa [B, U, T, goldbachG10BadActualAtoms, goldbachG10NonbadActualAtoms] using
      (Finset.sum_filter_add_sum_filter_not T (fun x : Σ _rs : ℕ × ℕ, ℕ => ¬Nat.Coprime x.2 N)
        (fun _ => (1 : ℤ)))
  have hsplit2 : (R.card : ℤ) + (V.card : ℤ) = (U.card : ℤ) := by
    simpa [R, V, U, goldbachG10RSquareActualAtoms, goldbachG10NoRSquareActualAtoms] using
      (Finset.sum_filter_add_sum_filter_not U (fun x : Σ _rs : ℕ × ℕ, ℕ => x.1.1 ^ 2 ∣ x.2)
        (fun _ => (1 : ℤ)))
  have hsplit3 : (S.card : ℤ) + (G.card : ℤ) = (V.card : ℤ) := by
    simpa [S, G, V, goldbachG10SSquareActualAtoms, goldbachG10GoodActualAtoms] using
      (Finset.sum_filter_add_sum_filter_not V (fun x : Σ _rs : ℕ × ℕ, ℕ => x.1.2 ^ 2 ∣ x.2)
        (fun _ => (1 : ℤ)))
  have hgood :
      (G.card : ℤ) ≤ goldbachPi10 N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) := by
    simpa [G] using goldbachG10GoodActualAtoms_card_le_goldbachPi10 hε hβ hβγ hγ hcut
  have hbad :
      (B.card : ℤ) ≤
        400 * goldbachBadCount (goldbachDifferenceCarrier N ε) N := by
    simpa [B] using goldbachG10BadActualAtoms_le_four_hundred_badCount
      (N := N) (ε := ε) (β := β) (γ := γ) hε (one_twentyfirst_lt_of_parameter_window hβ)
  have hr :
      (R.card : ℤ) ≤
        20 * goldbachQA (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) := by
    simpa [R] using goldbachG10RSquareActualAtoms_le_twenty_mul_goldbachQA
      (N := N) (ε := ε) (β := β) (γ := γ) hε (one_twentyfirst_lt_of_parameter_window hβ)
  have hs :
      (S.card : ℤ) ≤
        20 * goldbachQA (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) := by
    simpa [S] using goldbachG10SSquareActualAtoms_le_twenty_mul_goldbachQA
      (N := N) (ε := ε) (β := β) (γ := γ) hε (one_twentyfirst_lt_of_parameter_window hβ)
  omega

theorem exists_goldbachG10SwitchFinite_cutoff (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 1 < ε * (N : ℝ) ^ ((1 : ℝ) / 6) := by
  have hpow :
      Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < (1 : ℝ) / 6)).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, 1 < ε * ((N : ℝ) ^ ((1 : ℝ) / 6)) :=
    (hpow.const_mul_atTop hε).eventually (eventually_gt_atTop 1)
  exact Filter.Eventually.exists_forall_of_atTop hlarge

theorem goldbachG10Corrected_actual_eventually_le_pi10_with_errors
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ β γ : ℝ,
      (1 : ℝ) / 18 < β →
      β < (1 - 3 * β) / 3 →
      (1 - 3 * β) / 3 < γ →
      γ < (1 : ℝ) / 3 →
      goldbachG10Corrected (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) ≤
        goldbachPi10 N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) +
          400 * goldbachBadCount (goldbachDifferenceCarrier N ε) N +
          40 * goldbachQA (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) := by
  obtain ⟨N0, hN0⟩ := exists_goldbachG10SwitchFinite_cutoff ε hε
  refine ⟨N0, ?_⟩
  intro N hN β γ hβ hβγ hγ hγtop
  exact goldbachG10Corrected_actual_le_pi10_with_errors hε hβ hβγ hγ (hN0 N hN)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig