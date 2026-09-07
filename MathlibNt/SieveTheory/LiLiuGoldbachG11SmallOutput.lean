import MathlibNt.SieveTheory.LiLiuGoldbachG11BoundingSieve

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Finset
open scoped BigOperators
noncomputable section

/-- A fixed output determines m after the prime r has been retained. -/
theorem goldbachG11LinkedOutputFiber_injOn (N p : ℕ) (ε : ℝ) :
    Set.InjOn (fun x : GoldbachG11LinkedAtom => x.2)
      ((goldbachG11LinkedAtoms N ε).filter (fun x => goldbachG11LinkedOutput N x = p)) := by
  intro x hx y hy he
  obtain ⟨hx, hxp⟩ := mem_filter.mp hx
  obtain ⟨hy, hyp⟩ := mem_filter.mp hy
  obtain ⟨hxm, hxr⟩ := mem_sigma.mp hx
  obtain ⟨hym, hyr⟩ := mem_sigma.mp hy
  have hxl := goldbachG11LinkedPrimeWindow_product_le hxm hxr
  have hyl := goldbachG11LinkedPrimeWindow_product_le hym hyr
  have hrp := (mem_filter.mp hxr).2.1
  rcases x with ⟨m, r⟩
  rcases y with ⟨m', r'⟩
  dsimp at he
  subst r'
  dsimp at hxl hyl
  have hprod : r*m = r*m' := by
    dsimp [goldbachG11LinkedOutput] at hxp hyp
    omega
  have hmm : m = m' := Nat.eq_of_mul_eq_mul_left hrp.pos hprod
  subst m'
  rfl

theorem goldbachG11LinkedOutputFiber_card_le_twenty {N : ℕ} (hN : 2 ≤ N)
    (ε : ℝ) (p : ℕ) :
    ((goldbachG11LinkedAtoms N ε).filter (fun x => goldbachG11LinkedOutput N x = p)).card ≤ 20 := by
  classical
  let F := (goldbachG11LinkedAtoms N ε).filter (fun x => goldbachG11LinkedOutput N x = p)
  by_cases hF : F.Nonempty
  · obtain ⟨x, hx⟩ := hF
    obtain ⟨hxa, hxp⟩ := mem_filter.mp hx
    obtain ⟨hxm, hxr⟩ := mem_sigma.mp hxa
    have hm0 := (goldbachG11ProductSupport_data (mem_filter.mp hxm).1).1
    have hrp := (mem_filter.mp hxr).2.1
    have hprod0 : 0 < x.2*x.1 := Nat.mul_pos hrp.pos hm0
    have hprodN := goldbachG11LinkedPrimeWindow_product_le hxm hxr
    have hout0 := goldbachG11LinkedPrimeWindow_output_pos hxm hxr
    have hp0 : 0 < p := by
      change N-x.2*x.1 = p at hxp
      rw [hxp] at hout0
      exact hout0
    have hn0 : 1 ≤ N-p := by dsimp [goldbachG11LinkedOutput] at hxp; omega
    have hnN : N-p < N := by omega
    have hlarge := largePrimeDivisors_card_le_twenty hn0 hnN
      (by norm_num : (1 : ℝ)/21 < 4/53)
    refine (Finset.card_le_card_of_injOn (fun x : GoldbachG11LinkedAtom => x.2) ?_
      (goldbachG11LinkedOutputFiber_injOn N p ε)).trans hlarge
    intro y hy
    obtain ⟨hya, hyp⟩ := mem_filter.mp hy
    obtain ⟨hym, hyr⟩ := mem_sigma.mp hya
    have hyrp := (mem_filter.mp hyr).2.1
    have hymul := goldbachG11LinkedPrimeWindow_product_le hym hyr
    have heq : y.2*y.1 = N-p := by dsimp [goldbachG11LinkedOutput] at hyp; omega
    have hdiv : y.2 ∣ N-p := heq ▸ dvd_mul_right y.2 y.1
    have hz : (N : ℝ)^(4/53 : ℝ) ≤ (y.2 : ℝ) :=
      ((goldbachG11PiLiEndpoints_bounds hN hym).1.trans_lt (mem_filter.mp hyr).2.2.1).le
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hyrp, hdiv, by omega⟩, hz⟩
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ 20
    simp only [he, card_empty]
    omega

theorem goldbachG11LinkedOutputWeight_le_twenty {N : ℕ} (hN : 2 ≤ N)
    (ε : ℝ) (p : ℕ) : goldbachG11LinkedOutputWeight N ε p ≤ 20 := by
  calc
    _ ≤ ∑ _x ∈ (goldbachG11LinkedAtoms N ε).filter (fun x => goldbachG11LinkedOutput N x = p),
        (1 : ℝ) := sum_le_sum (fun x _ => (goldbachG11EffectiveProductCoefficient_bounds N x.1 ε).2)
    _ = (((goldbachG11LinkedAtoms N ε).filter (fun x => goldbachG11LinkedOutput N x = p)).card : ℝ) := by simp
    _ ≤ 20 := by exact_mod_cast goldbachG11LinkedOutputFiber_card_le_twenty hN ε p

def goldbachG11LinkedSmallOutputMass (N : ℕ) (ε Z : ℝ) : ℝ :=
  ∑ p ∈ (goldbachG11LinkedOutputSupport N ε).filter (fun p => p < Nat.ceil Z),
    goldbachG11LinkedOutputWeight N ε p

theorem goldbachG11LinkedSmallOutputMass_le {N : ℕ} (hN : 2 ≤ N) (ε Z : ℝ) :
    goldbachG11LinkedSmallOutputMass N ε Z ≤ 20*(Nat.ceil Z : ℝ) := by
  calc
    _ ≤ ∑ _p ∈ (goldbachG11LinkedOutputSupport N ε).filter (fun p => p < Nat.ceil Z),
        (20 : ℝ) := sum_le_sum (fun p _ => goldbachG11LinkedOutputWeight_le_twenty hN ε p)
    _ ≤ ∑ _p ∈ range (Nat.ceil Z), (20 : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact mem_range.mpr (mem_filter.mp hp).2
      · intro _ _ _; norm_num
    _ = 20*(Nat.ceil Z : ℝ) := by simp [mul_comm]

/-- Prime outputs survive the sieve unless they lie below its cutoff. -/
theorem goldbachG11LinkedPrimeOutput_le_sifted_add_small (N : ℕ) (ε Z : ℝ) :
    (∑ p ∈ (goldbachG11LinkedOutputSupport N ε).filter Nat.Prime,
      goldbachG11LinkedOutputWeight N ε p) ≤
      goldbachG11LinkedSiftedMass N ε Z + goldbachG11LinkedSmallOutputMass N ε Z := by
  classical
  have hsplit : (∑ p ∈ (goldbachG11LinkedOutputSupport N ε).filter Nat.Prime,
      goldbachG11LinkedOutputWeight N ε p) ≤
      (∑ p ∈ (goldbachG11LinkedOutputSupport N ε).filter
        (fun p => (goldbachB10ProdPrimes N Z).Coprime p), goldbachG11LinkedOutputWeight N ε p) +
      goldbachG11LinkedSmallOutputMass N ε Z := by
    simp only [goldbachG11LinkedSmallOutputMass, sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro p _
    have hw := goldbachG11LinkedOutputWeight_nonneg N ε p
    by_cases hp : p.Prime
    · rw [if_pos hp]
      by_cases hc : (goldbachB10ProdPrimes N Z).Coprime p
      · rw [if_pos hc]
        split_ifs <;> linarith
      · have hpd : p ∣ goldbachB10ProdPrimes N Z := by
          by_contra hpd
          exact hc ((hp.coprime_iff_not_dvd.mpr hpd).symm)
        have hsmall : p < Nat.ceil Z := Nat.lt_ceil.mpr
          (prime_dvd_goldbachB10ProdPrimes_lt hp hpd)
        simp only [if_neg hc, if_pos hsmall, zero_add, le_refl]
    · rw [if_neg hp]
      split_ifs <;> linarith
  simpa only [goldbachG11LinkedOutput_sum, goldbachG11LinkedSiftedMass] using hsplit

/-- Original good labelled count, with all multiplicity retained and the actual
small-output loss bounded; this is not yet an analytic upper-sieve estimate. -/
theorem goldbachG11GoodTotal_le_linkedSifted {N : ℕ} (hN : 2 ≤ N) (ε Z : ℝ) :
    (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
      400*goldbachG11LinkedSiftedMass N ε Z + 8000*(Nat.ceil Z : ℝ) := by
  classical
  have hsum : (∑ m ∈ goldbachG11EffectiveProductSupport N ε,
      goldbachG11EffectiveProductCoefficient N ε m *
        ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card : ℝ)) ≤
      ∑ m ∈ goldbachG11EffectiveProductSupport N ε,
      goldbachG11EffectiveProductCoefficient N ε m *
        (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => (N-r*m).Prime)).card : ℝ) := by
    apply sum_le_sum
    intro m hm
    have hc : (goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card ≤
        ((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => (N-r*m).Prime)).card := by
      apply card_le_card
      intro r hr
      have hr' : r ∈ (goldbachG11LinkedPrimeWindow N ε m).filter
          (fun r => ¬r ∣ N ∧ (N-r*m).Prime) :=
        (goldbachG11ProductFirstPrimeFiber_eq_linkedWindow hm) ▸ hr
      exact mem_filter.mpr ⟨(mem_filter.mp hr').1, (mem_filter.mp hr').2.2⟩
    have hcR : ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card : ℝ) ≤
        (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => (N-r*m).Prime)).card : ℝ) := by
      exact Nat.cast_le.mpr hc
    exact mul_le_mul_of_nonneg_left hcR (goldbachG11EffectiveProductCoefficient_bounds N m ε).1
  have hp := goldbachG11LinkedOutput_sum N ε Nat.Prime
  have hprime : (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
      400 * ∑ p ∈ (goldbachG11LinkedOutputSupport N ε).filter Nat.Prime,
        goldbachG11LinkedOutputWeight N ε p := by
    calc
      _ = 400 * ∑ m ∈ goldbachG11EffectiveProductSupport N ε,
          goldbachG11EffectiveProductCoefficient N ε m *
            ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card : ℝ) :=
        goldbachG11GoodSwitchedTotal_eq_effective_normalized_sum ε hN
      _ ≤ 400 * ∑ m ∈ goldbachG11EffectiveProductSupport N ε,
          goldbachG11EffectiveProductCoefficient N ε m *
            (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => (N-r*m).Prime)).card : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = _ := congrArg (fun t : ℝ => 400*t) hp.symm
  have hs := goldbachG11LinkedPrimeOutput_le_sifted_add_small N ε Z
  have he := goldbachG11LinkedSmallOutputMass_le hN ε Z
  linarith only [hprime, hs, he]

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig