import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryGridGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedWindowAP
import MathlibNt.SieveTheory.LiLiuFouvryG9IntegerFibre

open Finset
open scoped BigOperators Classical
open Wu2004MeanValue AnalyticNumberTheory.Sieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11OrdinaryAPWindow (N m : ℕ) (L U : ℝ) (d : ℕ) : Finset ℕ :=
  (primeSWInterval L U).filter (fun p => p.Prime ∧ m*p ≡ N [MOD d])

/-- Half-open prime interval with the original product congruence. -/
theorem goldbachG11OrdinaryAPWindow_eq_sdiff (N m d : ℕ) {L U : ℝ}
    (hm : 0 < m) (hL : 0 ≤ L) (hLU : L ≤ U) :
    goldbachG11OrdinaryAPWindow N m L U d =
      scaledPrimeSet ((m : ℝ)*U) d N m \ scaledPrimeSet ((m : ℝ)*L) d N m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hU := hL.trans hLU
  ext p
  simp only [goldbachG11OrdinaryAPWindow,primeSWInterval,mem_filter,mem_Ioc,mem_sdiff,
    mem_scaledPrimeSet (mul_nonneg hmR.le hU) hm,
    mem_scaledPrimeSet (mul_nonneg hmR.le hL) hm]
  constructor
  · rintro ⟨⟨hpl,hpu⟩,hp,hc⟩
    have hlp := (Nat.floor_lt hL).mp hpl
    have hpuR := (Nat.le_floor_iff hU).mp hpu
    refine ⟨⟨hp,mul_le_mul_of_nonneg_left hpuR hmR.le,hc⟩,?_⟩
    rintro ⟨_,hbad,_⟩
    have hh := mul_lt_mul_of_pos_left hlp hmR
    linarith
  · rintro ⟨⟨hp,hpu,hc⟩,hbad⟩
    have hlp : L < (p : ℝ) := by
      by_contra h
      exact hbad ⟨hp,mul_le_mul_of_nonneg_left (le_of_not_gt h) hmR.le,hc⟩
    have hpuR : (p : ℝ) ≤ U := (mul_le_mul_iff_right₀ hmR).mp hpu
    exact ⟨⟨(Nat.floor_lt hL).mpr hlp,(Nat.le_floor_iff hU).mpr hpuR⟩,hp,hc⟩

/-- Exact inverse residue and closed high endpoint, with no product≤N restriction. -/
theorem goldbachG11OrdinaryAPWindow_card_inverse (N m d : ℕ) {L U : ℝ}
    (hm : 0 < m) (hL : 0 ≤ L) (hLU : L ≤ U) (hmd : m.Coprime d) :
    ((goldbachG11OrdinaryAPWindow N m L U d).card : ℝ) =
      (primesInAP ⌊U⌋₊ d (natInvMod d m*N % d) : ℝ)-
        primesInAP ⌊L⌋₊ d (natInvMod d m*N % d) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hU := hL.trans hLU
  have hs : scaledPrimeSet ((m : ℝ)*L) d N m ⊆ scaledPrimeSet ((m : ℝ)*U) d N m := by
    intro p hp
    rw [mem_scaledPrimeSet (mul_nonneg hmR.le hL) hm] at hp
    rw [mem_scaledPrimeSet (mul_nonneg hmR.le hU) hm]
    exact ⟨hp.1,hp.2.1.trans (mul_le_mul_of_nonneg_left hLU hmR.le),hp.2.2⟩
  rw [goldbachG11OrdinaryAPWindow_eq_sdiff N m d hm hL hLU,
    card_sdiff_of_subset hs,Nat.cast_sub (card_le_card hs)]
  change (scaledPrimeCount _ d N m : ℝ)-scaledPrimeCount _ d N m = _
  rw [scaledPrimeCount_eq_inverse _ d N m (mul_nonneg hmR.le hU) hm hmd,
    scaledPrimeCount_eq_inverse _ d N m (mul_nonneg hmR.le hL) hm hmd]
  simp only [mul_div_cancel_left₀ _ (ne_of_gt hmR)]

/-- The literal absolute-difference divisibility row, including the zero and
negative-side possibilities, is the same finite prime AP window. -/
theorem goldbachG11OrdinaryAPWindow_row (N m d : ℕ) (L U : ℝ) :
    (∑ p ∈ primeSWInterval L U,
      primeSWBeta p*(if d ∣ ((N : ℤ)-(m : ℤ)*p).natAbs then 1 else 0)) =
      ((goldbachG11OrdinaryAPWindow N m L U d).card : ℝ) := by
  calc
    _ = ∑ p ∈ primeSWInterval L U, if p.Prime ∧ m*p ≡ N [MOD d] then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro p _
      have hdiv : d ∣ ((N : ℤ)-(m : ℤ)*p).natAbs ↔ m*p ≡ N [MOD d] := by
        simpa only [← Nat.cast_mul,Int.natCast_modEq_iff] using g9IntegerFibre_dvd_iff (N : ℤ) d m p
      by_cases hp : p.Prime <;> by_cases hc : m*p ≡ N [MOD d] <;> simp [primeSWBeta,hp,hdiv,hc]
    _ = ∑ _p ∈ goldbachG11OrdinaryAPWindow N m L U d, (1 : ℝ) := by
      simp only [goldbachG11OrdinaryAPWindow,sum_filter]
    _ = _ := by simp

theorem goldbachG11OrdinaryAPWindow_empty_of_not_coprime (N m d : ℕ) (L U : ℝ)
    (hNd : N.Coprime d) (hmd : ¬m.Coprime d) :
    goldbachG11OrdinaryAPWindow N m L U d = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hc := (mem_filter.mp hp).2.2
  have hg : (m*p).Coprime d := by
    change Nat.gcd (m*p) d = 1
    rw [hc.gcd_eq]
    exact hNd
  exact hmd (Nat.coprime_mul_iff_left.mp hg).1

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig