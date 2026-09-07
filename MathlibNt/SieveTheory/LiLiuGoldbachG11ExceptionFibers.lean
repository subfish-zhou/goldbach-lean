import MathlibNt.SieveTheory.LiLiuGoldbachG11RoughSandwich
import MathlibNt.SieveTheory.LiLiuGoldbachS5SwitchedCarrier

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11LabelCoordinates (v : GoldbachG11Label) : ℕ × ℕ × ℕ × ℕ :=
  (v.2.2.1, v.2.2.2, v.2.1, v.1)

theorem goldbachG11LabelCoordinates_injective :
    Function.Injective goldbachG11LabelCoordinates := by
  rintro ⟨t, s, r, q⟩ ⟨t', s', r', q'⟩ h
  have hc : r = r' ∧ q = q' ∧ s = s' ∧ t = t' := by
    simpa only [goldbachG11LabelCoordinates, Prod.mk.injEq] using h
  rcases hc with ⟨rfl, rfl, rfl, rfl⟩
  rfl

noncomputable def goldbachG11DivisorFiber (N n : ℕ) : Finset GoldbachG11Label := by
  classical
  exact (goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
    ((N : ℝ) ^ ((4 : ℝ) / 33))).filter fun v => goldbachG11LabelProd v ∣ n

theorem goldbachG11LabelCoordinates_mem_largePrimeDivisors
    {N n : ℕ} {v : GoldbachG11Label} (hn : n ≠ 0)
    (hv : v ∈ goldbachG11DivisorFiber N n) :
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

theorem goldbachG11DivisorFiber_card_le {N n : ℕ}
    (hn1 : 1 ≤ n) (hnN : n < N) :
    (goldbachG11DivisorFiber N n).card ≤ 160000 := by
  classical
  let L := largePrimeDivisors n ((N : ℝ) ^ ((4 : ℝ) / 53))
  have hcap : L.card ≤ 20 := largePrimeDivisors_card_le_twenty hn1 hnN
    (by norm_num : (1 : ℝ) / 21 < 4 / 53)
  have hcard : (goldbachG11DivisorFiber N n).card ≤
      (L.product (L.product (L.product L))).card :=
    Finset.card_le_card_of_injOn goldbachG11LabelCoordinates
      (fun _ hv => goldbachG11LabelCoordinates_mem_largePrimeDivisors (by omega) hv)
      (fun _ _ _ _ h => goldbachG11LabelCoordinates_injective h)
  calc
    (goldbachG11DivisorFiber N n).card ≤
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

theorem goldbachG11_difference_strict_bounds {N n : ℕ} {eps : ℝ}
    (heps : 0 ≤ eps) (hn : n ∈ goldbachDifferenceCarrier N eps) :
    1 ≤ n ∧ n < N := by
  obtain ⟨hn1, hnN, hp, _⟩ := goldbachG11_difference_data heps hn
  have hp0 := hp.pos
  exact ⟨hn1, by omega⟩

-- The sigma family retains the label even when several labels have the same product.
private theorem G11_sum_card_le (N : ℕ) (F : GoldbachG11Label → Finset ℕ)
    (T : Finset ℕ)
    (hT : ∀ n ∈ T, 1 ≤ n ∧ n < N)
    (hmap : ∀ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
        ((N : ℝ) ^ ((4 : ℝ) / 33)), ∀ n ∈ F v,
        n ∈ T ∧ goldbachG11LabelProd v ∣ n) :
    (∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
      ((N : ℝ) ^ ((4 : ℝ) / 33)), (F v).card) ≤ 160000 * T.card := by
  classical
  let X := (goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
    ((N : ℝ) ^ ((4 : ℝ) / 33))).sigma F
  have hmaps : ∀ x ∈ X, x.2 ∈ T := by
    intro x hx
    obtain ⟨hv, hn⟩ := Finset.mem_sigma.mp hx
    exact (hmap x.1 hv x.2 hn).1
  have hfiber : ∀ n ∈ T, (X.filter fun x => x.2 = n).card ≤ 160000 := by
    intro n hn
    have hto : Set.MapsTo (fun x : Σ _v : GoldbachG11Label, ℕ => x.1)
        (X.filter fun x => x.2 = n) (goldbachG11DivisorFiber N n) := by
      intro x hx
      obtain ⟨hx, heq⟩ := Finset.mem_filter.mp hx
      obtain ⟨hv, hxn⟩ := Finset.mem_sigma.mp hx
      exact Finset.mem_filter.mpr ⟨hv, heq ▸ (hmap x.1 hv x.2 hxn).2⟩
    have hinj : Set.InjOn (fun x : Σ _v : GoldbachG11Label, ℕ => x.1)
        (X.filter fun x => x.2 = n) := by
      intro x hx y hy hxy
      exact Sigma.ext hxy (heq_of_eq
        ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm))
    exact (Finset.card_le_card_of_injOn _ hto hinj).trans
      (goldbachG11DivisorFiber_card_le (hT n hn).1 (hT n hn).2)
  have hfilter : X.filter (fun x => x.2 ∈ T) = X := Finset.filter_eq_self.mpr hmaps
  have heq : (∑ n ∈ T, (X.filter fun x => x.2 = n).card) = X.card := by
    simpa [hfilter] using
      Finset.sum_fiberwise_eq_sum_filter X T (fun x => x.2) (fun _ => (1 : ℕ))
  calc
    _ = X.card := (Finset.card_sigma _ _).symm
    _ = ∑ n ∈ T, (X.filter fun x => x.2 = n).card := heq.symm
    _ ≤ ∑ _n ∈ T, 160000 := Finset.sum_le_sum hfiber
    _ = 160000 * T.card := by simp [mul_comm]

theorem goldbachG11RSquareCount_sum_le (N : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
    (∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
      ((N : ℝ) ^ ((4 : ℝ) / 33)),
      goldbachG11RSquareCount (goldbachDifferenceCarrier N eps) v) ≤
        160000 * goldbachS5SquareCount N := by
  classical
  have h := G11_sum_card_le N
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

theorem goldbachG11NCount_sum_le (N : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
    (∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ ((4 : ℝ) / 53))
      ((N : ℝ) ^ ((4 : ℝ) / 33)),
      goldbachG11NCount (goldbachDifferenceCarrier N eps) N v) ≤
        160000 * goldbachBadCount (goldbachDifferenceCarrier N eps) N := by
  classical
  let T := (goldbachDifferenceCarrier N eps).filter fun n => ¬Nat.Coprime n N
  have h := G11_sum_card_le N
    (goldbachG11NException (goldbachDifferenceCarrier N eps) N) T
    (fun _ hn => goldbachG11_difference_strict_bounds heps (Finset.mem_filter.mp hn).1)
    (by
      intro v _ n hn
      obtain ⟨hnA, hd, hbad⟩ := Finset.mem_filter.mp hn
      exact ⟨Finset.mem_filter.mpr ⟨hnA, hbad⟩, hd⟩)
  unfold goldbachG11NCount goldbachBadCount
  exact_mod_cast h

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig