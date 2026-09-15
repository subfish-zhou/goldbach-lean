import MathlibNt.Wu2008DoubleSieve.NinthSwitchingCountExceptions

/-!
# A bounded finite ninth-term switching theorem

The good atoms inject into the cutoff-preserving labelled triple carrier.
The three explicitly counted exceptional families have respective budgets
`(sqrt N + 1)/k2^2`, `2*N^(1-k2)/k2^2`, and `N^(1-k1)/k2^2`.
This is a finite counting theorem, not an analytic estimate for `F9`.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def ninthGoodAtoms (N : ℕ) (w u : ℝ) : Finset NinthLabel :=
  (ninthAtoms N w u).filter (fun x =>
    ¬x.2 ∣ N ∧ ¬x.1.1 ^ 2 ∣ N - x.2 ∧ u ≤ (ninthCofactor N x : ℝ))

def ninthSwitch (N : ℕ) (x : NinthLabel) : NinthLabel :=
  ⟨x.1, ninthCofactor N x⟩

/-- Switching preserves the pair labels. The cutoff excludes the unit
alternative, and `a*b*m = N-r` recovers the bounded prime index. -/
theorem ninthGoodAtoms_card_le_T9 {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (w u : ℝ) :
    (ninthGoodAtoms N w u).card ≤ (T9 N w u).card := by
  apply card_le_card_of_injOn (ninthSwitch N)
  · intro x hx
    obtain ⟨hx, hrnot, hsnot, hmu⟩ := mem_filter.mp hx
    obtain ⟨ht, hr⟩ := mem_ninthAtoms.mp hx
    obtain ⟨hpair, hau⟩ := mem_filter.mp ht
    obtain ⟨ha, hb, _⟩ := mem_lowerPairs_source.mp hpair
    obtain ⟨hrN, hrp⟩ := mem_primeIndices.mp (ninthAtom_index hx)
    have hm : (ninthCofactor N x).Prime := by
      rcases ninth_cofactor_one_or_prime hN he ha hb hr hrnot hsnot with h1 | hp
      · have ha2 : (2 : ℝ) ≤ x.1.1 := by exact_mod_cast ha.two_le
        have hc1 : (ninthCofactor N x : ℝ) = 1 := by exact_mod_cast h1
        linarith
      · exact hp
    have hmul := ninthAtom_mul_cofactor hx
    apply mem_T9.mpr
    refine ⟨ht, hm, hmu, ?_, ?_⟩
    · change x.1.1 * x.1.2 * ninthCofactor N x < N
      rw [hmul]
      exact Nat.sub_lt (by omega) hrp.pos
    · change (N - x.1.1 * x.1.2 * ninthCofactor N x).Prime
      rwa [hmul, Nat.sub_sub_self hrN]
  · intro x hx y hy h
    have hxA := (mem_filter.mp hx).1
    have hyA := (mem_filter.mp hy).1
    have ht := congrArg (fun z : NinthLabel => z.1) h
    change x.1 = y.1 at ht
    have hc : ninthCofactor N x = ninthCofactor N y :=
      congrArg (fun z : NinthLabel => z.2) h
    have hn : N - x.2 = N - y.2 := by
      calc
        N - x.2 = x.1.1 * x.1.2 * ninthCofactor N x :=
          (ninthAtom_mul_cofactor hxA).symm
        _ = y.1.1 * y.1.2 * ninthCofactor N y := by rw [hc, ht]
        _ = N - y.2 := ninthAtom_mul_cofactor hyA
    have hxN := (mem_primeIndices.mp (ninthAtom_index hxA)).1
    have hyN := (mem_primeIndices.mp (ninthAtom_index hyA)).1
    exact Sigma.ext ht (heq_of_eq (by omega))

/-- The exceptions may overlap; the union bound needs no disjointness
and counts all three of them. -/
theorem ninthAtoms_card_le_parts (N : ℕ) (w u : ℝ) :
    (ninthAtoms N w u).card ≤
      (ninthGoodAtoms N w u).card + (ninthDivisorAtoms N w u).card +
        (ninthSquareAtoms N w u).card + (ninthSmallAtoms N w u).card := by
  let A := ninthAtoms N w u
  let G := ninthGoodAtoms N w u
  let D := ninthDivisorAtoms N w u
  let S := ninthSquareAtoms N w u
  let M := ninthSmallAtoms N w u
  have hcover : A ⊆ ((G ∪ D) ∪ S) ∪ M := by
    intro x hx
    simp only [mem_union]
    by_cases hd : x.2 ∣ N
    · exact Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨hx, hd⟩)))
    by_cases hs : x.1.1 ^ 2 ∣ N - x.2
    · exact Or.inl (Or.inr (mem_filter.mpr ⟨hx, hs⟩))
    by_cases hm : (ninthCofactor N x : ℝ) < u
    · exact Or.inr (mem_filter.mpr ⟨hx, hm⟩)
    exact Or.inl (Or.inl (Or.inl
      (mem_filter.mpr ⟨hx, hd, hs, le_of_not_gt hm⟩)))
  have h0 := card_le_card hcover
  have h1 := card_union_le (s := (G ∪ D) ∪ S) (t := M)
  have h2 := card_union_le (s := G ∪ D) (t := S)
  have h3 := card_union_le (s := G) (t := D)
  change A.card ≤ G.card + D.card + S.card + M.card
  omega

/-- The stronger finite budget before scalar absorption. No count or
multiplicity bound is an input: all three budgets are proved above. -/
theorem variableS3Main_le_T9_add_finite_budget {N : ℕ} {k1 k2 : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hk1 : 1 / 14 ≤ k1)
    (hk2 : 0 < k2) (hw : 2 ≤ (N : ℝ) ^ k2) :
    (variableS3Main N ((N : ℝ) ^ k2) ((N : ℝ) ^ (1 / 2 - 3 * k1)) : ℝ) ≤
      ((T9 N ((N : ℝ) ^ k2) ((N : ℝ) ^ (1 / 2 - 3 * k1))).card : ℝ) +
        (1 / k2 ^ 2) * (Real.sqrt N + 1) +
        (2 / k2 ^ 2) * (N : ℝ) ^ (1 - k2) +
        (1 / k2 ^ 2) * (N : ℝ) ^ (1 - k1) := by
  let w := (N : ℝ) ^ k2
  let u := (N : ℝ) ^ (1 / 2 - 3 * k1)
  have hparts :
      ((ninthAtoms N w u).card : ℝ) ≤
        ((ninthGoodAtoms N w u).card : ℝ) + (ninthDivisorAtoms N w u).card +
          (ninthSquareAtoms N w u).card + (ninthSmallAtoms N w u).card := by
    exact_mod_cast ninthAtoms_card_le_parts N w u
  rw [ninthAtoms_card] at hparts
  have hg : ((ninthGoodAtoms N w u).card : ℝ) ≤ (T9 N w u).card := by
    exact_mod_cast ninthGoodAtoms_card_le_T9 hN he w u
  have hd := ninthDivisorAtoms_card_le (u := u) hN he hk2
  have hs := ninthSquareAtoms_card_le (u := u) hN he hk2 hw
  have hm := ninthSmallAtoms_card_le hN he hk1 hk2
  dsimp only [w, u] at hparts hg hd hs
  linarith

theorem ninth_sqrt_budget_le {N : ℕ} {k : ℝ}
    (hN : 1 ≤ N) (hk : k ≤ 1 / 3) :
    Real.sqrt N + 1 ≤ 2 * (N : ℝ) ^ (1 - k) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : Real.sqrt N ≤ (N : ℝ) ^ (1 - k) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - k) := by
    have h := Real.rpow_le_rpow_of_exponent_le hN1
      (show (0 : ℝ) ≤ 1 - k by linarith)
    simpa only [Real.rpow_zero] using h
  linarith

/-- The concrete finite ninth-term switching theorem on the required
cutoff-preserving parameter domain. -/
theorem variableS3Main_le_T9_add_error {N : ℕ} {k1 k2 : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hk1 : 1 / 14 ≤ k1)
    (hk1_upper : k1 ≤ 1 / 3) (h12 : k1 ≤ k2)
    (hw : 2 ≤ (N : ℝ) ^ k2) :
    (variableS3Main N ((N : ℝ) ^ k2) ((N : ℝ) ^ (1 / 2 - 3 * k1)) : ℝ) ≤
      ((T9 N ((N : ℝ) ^ k2) ((N : ℝ) ^ (1 / 2 - 3 * k1))).card : ℝ) +
        (5 / k2 ^ 2) * (N : ℝ) ^ (1 - k1) := by
  have hk2 : 0 < k2 := by linarith
  have h := variableS3Main_le_T9_add_finite_budget hN he hk1 hk2 hw
  have hs := mul_le_mul_of_nonneg_left
    (ninth_sqrt_budget_le (by omega : 1 ≤ N) hk1_upper)
    (show (0 : ℝ) ≤ 1 / k2 ^ 2 by positivity)
  have hp := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega) : (1 : ℝ) ≤ N)
      (show 1 - k2 ≤ 1 - k1 by linarith))
    (show (0 : ℝ) ≤ 2 / k2 ^ 2 by positivity)
  calc
    _ ≤ ((T9 N ((N : ℝ) ^ k2) ((N : ℝ) ^ (1 / 2 - 3 * k1))).card : ℝ) +
        (1 / k2 ^ 2) * (2 * (N : ℝ) ^ (1 - k1)) +
        (2 / k2 ^ 2) * (N : ℝ) ^ (1 - k1) +
        (1 / k2 ^ 2) * (N : ℝ) ^ (1 - k1) := by linarith
    _ = _ := by ring

theorem ninth_switching_final_parameters :
    (1 / 14 : ℝ) ≤ 100 / 1327 ∧ (100 / 1327 : ℝ) ≤ 1 / 3 ∧
      (100 / 1327 : ℝ) ≤ 25 / 206 := by
  norm_num

end Wu2008DoubleSieve
