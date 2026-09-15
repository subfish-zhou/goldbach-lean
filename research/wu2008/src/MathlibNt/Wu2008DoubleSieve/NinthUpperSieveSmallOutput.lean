import MathlibNt.Wu2008DoubleSieve.NinthUpperSieveDefinitions

/-!
# Small prime outputs with all ninth-term labels retained

This counts T9 directly, not as a subset of the old sieve atoms.
Fixing the output and selected pair recovers the varying prime.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

def ninthOutput (N : ℕ) (x : NinthLabel) : ℕ := N - x.1.1 * x.1.2 * x.2

noncomputable def ninthSmallOutputLabels (N : ℕ) (Z : ℝ) : Finset NinthLabel :=
  (T9 N (ninthProfileW N) (ninthProfileU N)).filter (fun x => (ninthOutput N x : ℝ) < Z)

noncomputable def ninthSmallOutputBudget (Z : ℝ) : ℝ :=
  (1 / ninthProfileK2 ^ 2) * (⌊max Z 0⌋₊ + 1 : ℕ)

theorem ninthOutput_properties {N : ℕ} {x : NinthLabel}
    (hx : x ∈ T9 N (ninthProfileW N) (ninthProfileU N)) :
    (ninthOutput N x).Prime ∧ ninthOutput N x ≤ N ∧
      N - ninthOutput N x = x.1.1 * x.1.2 * x.2 := by
  obtain ⟨_, _, _, hs, hp⟩ := mem_T9.mp hx
  exact ⟨hp, Nat.sub_le _ _, Nat.sub_sub_self hs.le⟩

/-- This injection does not discard or try to recover pair labels from
the output alone: it explicitly keeps the pair as a coordinate. -/
theorem ninthOutput_pair_injOn (N : ℕ) :
    Set.InjOn (fun x : NinthLabel =>
      (⟨ninthOutput N x, x.1⟩ : Sigma (fun _ : ℕ => ℕ × ℕ)))
      (T9 N (ninthProfileW N) (ninthProfileU N)) := by
  intro x hx y hy h
  have hr := congrArg Sigma.fst h
  have ht := congrArg (fun z : Sigma (fun _ : ℕ => ℕ × ℕ) => z.2) h
  have hprod : x.1.1 * x.1.2 * x.2 = y.1.1 * y.1.2 * y.2 := by
    rw [← (ninthOutput_properties hx).2.2, ← (ninthOutput_properties hy).2.2]
    exact congrArg (fun r => N - r) hr
  have hpos := ninthPair_product_pos (mem_T9.mp hx).1
  change 0 < x.1.1 * x.1.2 at hpos
  change x.1 = y.1 at ht
  rw [← ht] at hprod
  have hc : x.2 = y.2 := by nlinarith
  exact Sigma.ext ht (heq_of_eq hc)

theorem ninthOutput_pair_divisors {N : ℕ} {x : NinthLabel}
    (hx : x ∈ T9 N (ninthProfileW N) (ninthProfileU N))
    (hn : 0 < N - ninthOutput N x) :
    x.1 ∈ largePrimeDivisors (N - ninthOutput N x) (ninthProfileW N) ×ˢ
      largePrimeDivisors (N - ninthOutput N x) (ninthProfileW N) := by
  obtain ⟨ha, hb, _, hwa, _, hab, _⟩ :=
    mem_lowerPairs_source.mp (mem_filter.mp (mem_T9.mp hx).1).1
  have hd : x.1.1 * x.1.2 ∣ N - ninthOutput N x := by
    rw [(ninthOutput_properties hx).2.2]
    exact dvd_mul_right _ _
  exact mem_product.mpr
    ⟨mem_largePrimeDivisors.mpr
      ⟨ha, (dvd_mul_right _ _).trans hd, hn.ne', hwa⟩,
     mem_largePrimeDivisors.mpr
      ⟨hb, (dvd_mul_left _ _).trans hd, hn.ne',
        hwa.trans (by exact_mod_cast hab.le)⟩⟩

theorem ninthSmallOutputLabels_card_le {N : ℕ} (hN : 512 ≤ N) (he : Even N) (Z : ℝ) :
    ((ninthSmallOutputLabels N Z).card : ℝ) ≤ ninthSmallOutputBudget Z := by
  let S := (range (⌊max Z 0⌋₊ + 1)).filter (fun r => r.Prime ∧ r ≤ N)
  let F := fun r => largePrimeDivisors (N - r) (ninthProfileW N)
  have hinj : (ninthSmallOutputLabels N Z).card ≤
      (S.sigma (fun r => F r ×ˢ F r)).card := by
    apply card_le_card_of_injOn (fun x : NinthLabel =>
      (⟨ninthOutput N x, x.1⟩ : Sigma (fun _ : ℕ => ℕ × ℕ)))
    · intro x hx
      obtain ⟨hx, hZ⟩ := mem_filter.mp hx
      obtain ⟨hrp, hrN, _⟩ := ninthOutput_properties hx
      have hrsmall : ninthOutput N x ≤ ⌊max Z 0⌋₊ :=
        Nat.le_floor (hZ.le.trans (le_max_left _ _))
      exact mem_sigma.mpr
        ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hrsmall), hrp, hrN⟩,
          ninthOutput_pair_divisors hx (complement_pos_of_even (by omega) he hrN hrp)⟩
    · exact (ninthOutput_pair_injOn N).mono (filter_subset _ _)
  calc
    ((ninthSmallOutputLabels N Z).card : ℝ) ≤
        ((S.sigma (fun r => F r ×ˢ F r)).card : ℝ) := by exact_mod_cast hinj
    _ = ∑ r ∈ S, ((F r ×ˢ F r).card : ℝ) := by rw [card_sigma, Nat.cast_sum]
    _ ≤ ∑ _r ∈ S, (1 / ninthProfileK2 ^ 2 : ℝ) := by
      apply sum_le_sum
      intro r hr
      obtain ⟨_, hrp, hrN⟩ := mem_filter.mp hr
      exact ninth_pair_budget (by omega)
        (complement_pos_of_even (by omega) he hrN hrp) (Nat.sub_le N r)
        (by norm_num [ninthProfileK2])
    _ = (1 / ninthProfileK2 ^ 2) * S.card := by
      simp only [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ninthSmallOutputBudget Z := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hc : S.card ≤ ⌊max Z 0⌋₊ + 1 := by
        simpa only [card_range] using (card_le_card (filter_subset _ _) : S.card ≤
          (range (⌊max Z 0⌋₊ + 1)).card)
      exact_mod_cast hc

theorem ninth_prime_sifted {N r : ℕ} {Z : ℝ} (hr : r.Prime) (hZ : Z ≤ (r : ℝ)) :
    Sifted N r Z := by
  intro q hq _ hqZ hd
  have hqr : q = r := ((Nat.dvd_prime hr).mp hd).resolve_left hq.ne_one
  subst q
  linarith

theorem ninthT9_large_outputs_le_sifted (N : ℕ) (Z : ℝ) :
    (((T9 N (ninthProfileW N) (ninthProfileU N)).filter
      (fun x => ¬(ninthOutput N x : ℝ) < Z)).card : ℝ) ≤ ninthSiftedCount N Z := by
  let G := (ninthProductSupport N).sigma
    (fun m => (P9 N m).filter (fun c => Sifted N (N - m * c) Z))
  have hinj : ((T9 N (ninthProfileW N) (ninthProfileU N)).filter
      (fun x => ¬(ninthOutput N x : ℝ) < Z)).card ≤ G.card := by
    apply card_le_card_of_injOn (fun x : NinthLabel =>
      (⟨ninthPairProduct x.1, x.2⟩ : Sigma (fun _ : ℕ => ℕ)))
    · intro x hx
      obtain ⟨hx, hZ⟩ := mem_filter.mp hx
      have ht := (mem_T9.mp hx).1
      have hcf := (mem_sigma.mp hx).2
      rw [ninthPair_fibre_eq_profile ht] at hcf
      exact mem_sigma.mpr ⟨mem_image.mpr ⟨x.1, ht, rfl⟩,
        mem_filter.mpr ⟨(mem_filter.mp hcf).1,
          ninth_prime_sifted (ninthOutput_properties hx).1 (le_of_not_gt hZ)⟩⟩
    · intro x hx y hy h
      have hprod := congrArg Sigma.fst h
      have ht := ninthPairProduct_injOn N (ninthProfileW N) (ninthProfileU N)
        (mem_T9.mp (mem_filter.mp hx).1).1 (mem_T9.mp (mem_filter.mp hy).1).1 hprod
      have hc := congrArg (fun z : Sigma (fun _ : ℕ => ℕ) => z.2) h
      exact Sigma.ext ht (heq_of_eq hc)
  have hcard : (G.card : ℝ) = ninthSiftedCount N Z := by
    simp only [G, card_sigma, Nat.cast_sum, ninthSiftedCount]
  exact (by exact_mod_cast hinj : (_ : ℝ) ≤ (G.card : ℝ)).trans_eq hcard

theorem T9_card_le_sifted_add_small {N : ℕ} (hN : 512 ≤ N) (he : Even N) (Z : ℝ) :
    ((T9 N (ninthProfileW N) (ninthProfileU N)).card : ℝ) ≤
      ninthSiftedCount N Z + ninthSmallOutputBudget Z := by
  have hsplit := card_filter_add_card_filter_not
    (s := T9 N (ninthProfileW N) (ninthProfileU N))
    (fun x => (ninthOutput N x : ℝ) < Z)
  have hsplitR :
      ((ninthSmallOutputLabels N Z).card : ℝ) +
        (((T9 N (ninthProfileW N) (ninthProfileU N)).filter
          (fun x => ¬(ninthOutput N x : ℝ) < Z)).card : ℝ) =
        (T9 N (ninthProfileW N) (ninthProfileU N)).card := by exact_mod_cast hsplit
  have hs := ninthSmallOutputLabels_card_le hN he Z
  have hl := ninthT9_large_outputs_le_sifted N Z
  linarith

end Wu2008DoubleSieve
