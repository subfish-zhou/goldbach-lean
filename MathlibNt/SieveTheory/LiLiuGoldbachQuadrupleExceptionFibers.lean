import MathlibNt.SieveTheory.FiniteLabelCounting
import MathlibNt.SieveTheory.LiLiuGoldbachG11ExceptionFibers
import MathlibNt.SieveTheory.LiLiuGoldbachS5SwitchedCarrier

/- The accepted G11 fibre proof only uses the lower prime cutoff.
This parameter-polymorphic version retains its proof for every upper cutoff. -/

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachQuadrupleDivisorFiber (N n : ℕ) (b : ℝ) : Finset GoldbachG11Label := by
  classical
  exact (goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
    b).filter fun v => goldbachG11LabelProd v ∣ n

theorem goldbachQuadrupleCoordinates_mem_largePrimeDivisors
    {N n : ℕ} {b : ℝ} {v : GoldbachG11Label} (hn : n ≠ 0)
    (hv : v ∈ goldbachQuadrupleDivisorFiber N n b) :
    goldbachG11LabelCoordinates v ∈
      (largePrimeDivisors n ((N : ℝ) ^ ((4 : ℝ) / 53))).product
        ((largePrimeDivisors n ((N : ℝ) ^ ((4 : ℝ) / 53))).product
          ((largePrimeDivisors n ((N : ℝ) ^ ((4 : ℝ) / 53))).product
            (largePrimeDivisors n ((N : ℝ) ^ ((4 : ℝ) / 53))))) := by
  classical
  rcases v with ⟨t, s, r, q⟩
  obtain ⟨hv, hd⟩ := Finset.mem_filter.mp hv
  rcases mem_goldbachG11Labels_iff.mp hv with
    ⟨hr, hq, hs, ht, _, hlo, hrq, hqs, hst, _⟩
  change r * q * s * t ∣ n at hd
  have hrn : r ∣ n :=
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right r q) s) t).trans hd
  have hqn : q ∣ n :=
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left q r) s) t).trans hd
  have hsn : s ∣ n := (dvd_mul_of_dvd_left (dvd_mul_left s (r * q)) t).trans hd
  have htn : t ∣ n := (dvd_mul_left t (r * q * s)).trans hd
  have hql : (N : ℝ) ^ ((4 : ℝ) / 53) ≤ (q : ℝ) :=
    hlo.trans (by exact_mod_cast hrq)
  have hsl : (N : ℝ) ^ ((4 : ℝ) / 53) ≤ (s : ℝ) :=
    hql.trans (by exact_mod_cast hqs)
  have htl : (N : ℝ) ^ ((4 : ℝ) / 53) ≤ (t : ℝ) :=
    hsl.trans (by exact_mod_cast hst)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hr, hrn, hn⟩, hlo⟩,
      Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq, hqn, hn⟩, hql⟩,
          Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hs, hsn, hn⟩, hsl⟩,
              Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨ht, htn, hn⟩, htl⟩⟩⟩⟩

theorem goldbachQuadrupleDivisorFiber_card_le {N n : ℕ} {b : ℝ}
    (hn1 : 1 ≤ n) (hnN : n < N) :
    (goldbachQuadrupleDivisorFiber N n b).card ≤ 160000 := by
  classical
  let L := largePrimeDivisors n ((N : ℝ) ^ ((4 : ℝ) / 53))
  have hcap : L.card ≤ 20 := largePrimeDivisors_card_le_twenty hn1 hnN
    (by norm_num : (1 : ℝ) / 21 < 4 / 53)
  have hcard : (goldbachQuadrupleDivisorFiber N n b).card ≤
      (L.product (L.product (L.product L))).card :=
    Finset.card_le_card_of_injOn goldbachG11LabelCoordinates
      (fun _ hv => goldbachQuadrupleCoordinates_mem_largePrimeDivisors (by omega) hv)
      (fun _ _ _ _ h => goldbachG11LabelCoordinates_injective h)
  calc
    (goldbachQuadrupleDivisorFiber N n b).card ≤
        (L.product (L.product (L.product L))).card := hcard
    _ = L.card * (L.product (L.product L)).card := Finset.card_product _ _
    _ = L.card * (L.card * (L.card * L.card)) := by
      congr 1
      calc
        (L.product (L.product L)).card = L.card * (L.product L).card :=
          Finset.card_product _ _
        _ = L.card * (L.card * L.card) := congrArg (L.card * ·) (Finset.card_product L L)
    _ = L.card ^ 4 := by ring
    _ ≤ 20 ^ 4 := Nat.pow_le_pow_left hcap 4
    _ = 160000 := by norm_num

-- The sigma family retains the label even when several labels have the same product.
private theorem Quadruple_sum_card_le (N : ℕ) (b : ℝ) (F : GoldbachG11Label → Finset ℕ)
    (T : Finset ℕ)
    (hT : ∀ n ∈ T, 1 ≤ n ∧ n < N)
    (hmap : ∀ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
        b, ∀ n ∈ F v,
        n ∈ T ∧ goldbachG11LabelProd v ∣ n) :
    (∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
      b, (F v).card) ≤ 160000 * T.card := by
  classical
  exact sum_card_le_of_relation _ T F (fun v n => goldbachG11LabelProd v ∣ n)
    160000 hmap (fun n hn => goldbachQuadrupleDivisorFiber_card_le (hT n hn).1 (hT n hn).2)

theorem goldbachQuadrupleRSquareCount_sum_le (N : ℕ) (eps b : ℝ) (heps : 0 ≤ eps) :
    (∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
      b,
      goldbachG11RSquareCount (goldbachDifferenceCarrier N eps) v) ≤
        160000 * goldbachS5SquareCount N := by
  classical
  have h := Quadruple_sum_card_le N b
    (goldbachG11RSquareException (goldbachDifferenceCarrier N eps))
    (goldbachS5SquareSet N) (fun n hn => by
      obtain ⟨hn0, hnN, _⟩ := mem_goldbachS5SquareSet_iff.mp hn
      exact ⟨hn0, hnN⟩) (by
      intro v hv n hn
      obtain ⟨hnA, hd, _, hsq⟩ := Finset.mem_filter.mp hn
      have hb := goldbachG11_difference_strict_bounds heps hnA
      rcases v with ⟨t, s, r, q⟩
      have hp := mem_goldbachG11Labels_iff.mp hv
      exact ⟨mem_goldbachS5SquareSet_iff.mpr
        ⟨hb.1, hb.2, r, hp.1, hp.2.2.2.2.2.1, hsq⟩, hd⟩)
  unfold goldbachG11RSquareCount goldbachS5SquareCount
  exact_mod_cast h

theorem goldbachQuadrupleNCount_sum_le (N : ℕ) (eps b : ℝ) (heps : 0 ≤ eps) :
    (∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
      b,
      goldbachG11NCount (goldbachDifferenceCarrier N eps) N v) ≤
        160000 * goldbachBadCount (goldbachDifferenceCarrier N eps) N := by
  classical
  let T := (goldbachDifferenceCarrier N eps).filter fun n => ¬Nat.Coprime n N
  have h := Quadruple_sum_card_le N b
    (goldbachG11NException (goldbachDifferenceCarrier N eps) N) T
    (fun _ hn => goldbachG11_difference_strict_bounds heps (Finset.mem_filter.mp hn).1)
    (by
      intro v _ n hn
      obtain ⟨hnA, hd, hbad⟩ := Finset.mem_filter.mp hn
      exact ⟨Finset.mem_filter.mpr ⟨hnA, hbad⟩, hd⟩)
  unfold goldbachG11NCount goldbachBadCount
  exact_mod_cast h

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig