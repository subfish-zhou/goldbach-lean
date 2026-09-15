import MathlibNt.Wu2008DoubleSieve.SeventhEighthFiniteSwitching

/-! Exception counts are counts of actual prime/label atoms. The shared
large-prime divisor and square-multiple estimates are used without changing
any ninth-term domain. -/
namespace Wu2008DoubleSieve.SeventhEighth
open Finset Real

/-- A small structural domain interface, with no counting or payment premise. -/
def PairDomain (N : ℕ) (k : ℝ) (D : Finset (ℕ × ℕ)) : Prop :=
  ∀ t ∈ D, Nat.Prime t.1 ∧ Nat.Prime t.2 ∧ (N : ℝ) ^ k ≤ t.1 ∧
    t.1 < t.2 ∧ t.1 * t.2 ^ 2 < N

theorem atom_pair_divisors {N : ℕ} {k : ℝ} {D : Finset (ℕ × ℕ)}
    (hD : PairDomain N k D) {x : NinthLabel} (hx : x ∈ atoms N D)
    (hn : 0 < N - x.2) :
    x.1 ∈ largePrimeDivisors (N - x.2) ((N : ℝ) ^ k) ×ˢ
      largePrimeDivisors (N - x.2) ((N : ℝ) ^ k) := by
  obtain ⟨ha, hb, hka, hab, _⟩ := hD x.1 (mem_atoms.mp hx).1
  have hd := (atom_data hx).2.2
  have hkb : (N : ℝ) ^ k ≤ x.1.2 := hka.trans (by exact_mod_cast hab.le)
  exact mem_product.mpr ⟨mem_largePrimeDivisors.mpr
    ⟨ha, (dvd_mul_right _ _).trans hd, hn.ne', hka⟩,
    mem_largePrimeDivisors.mpr ⟨hb, (dvd_mul_left _ _).trans hd, hn.ne', hkb⟩⟩

theorem card_le_indices {N : ℕ} {k : ℝ} {D : Finset (ℕ × ℕ)}
    (hN : 4 ≤ N) (he : Even N) (hk : 0 < k) (hD : PairDomain N k D)
    {A : Finset NinthLabel} (hA : A ⊆ atoms N D) {S : Finset ℕ}
    (hindex : ∀ x ∈ A, x.2 ∈ S) :
    (A.card : ℝ) ≤ 1 / k ^ 2 * S.card := by
  classical
  have hcard := card_eq_sum_card_fiberwise hindex
  rw [hcard, Nat.cast_sum]
  calc
    _ ≤ ∑ _p ∈ S, (1 / k ^ 2 : ℝ) := by
      apply sum_le_sum
      intro p _
      let F := A.filter fun x => x.2 = p
      by_cases hF : F.Nonempty
      · obtain ⟨x, hx⟩ := hF
        obtain ⟨hxA, hxp⟩ := mem_filter.mp hx
        obtain ⟨hpN, hpp, _⟩ := atom_data (hA hxA)
        rw [hxp] at hpN hpp
        have hn := complement_pos_of_even hN he hpN hpp
        have hinj : F.card ≤ (largePrimeDivisors (N - p) ((N : ℝ) ^ k) ×ˢ
            largePrimeDivisors (N - p) ((N : ℝ) ^ k)).card := by
          apply card_le_card_of_injOn (fun y : NinthLabel => y.1)
          · intro y hy
            obtain ⟨hyA, hyp⟩ := mem_filter.mp hy
            have := atom_pair_divisors hD (hA hyA) (by simpa only [hyp] using hn)
            simpa only [Finset.mem_coe, hyp] using this
          · intro y hy z hz hyz
            have hyp := (mem_filter.mp hy).2
            have hzp := (mem_filter.mp hz).2
            exact Sigma.ext hyz (heq_of_eq (hyp.trans hzp.symm))
        exact (show (F.card : ℝ) ≤ _ by exact_mod_cast hinj).trans
          (ninth_pair_budget (by omega) hn (Nat.sub_le _ _) hk)
      · have hz : F = ∅ := not_nonempty_iff_eq_empty.mp hF
        change (F.card : ℝ) ≤ _
        rw [hz, card_empty, Nat.cast_zero]
        positivity
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

theorem card_le_complements {N : ℕ} {k : ℝ} {D : Finset (ℕ × ℕ)}
    (hN : 4 ≤ N) (he : Even N) (hk : 0 < k) (hD : PairDomain N k D)
    {A : Finset NinthLabel} (hA : A ⊆ atoms N D) {E : Finset ℕ}
    (hcomp : ∀ x ∈ A, N - x.2 ∈ E) :
    (A.card : ℝ) ≤ 1 / k ^ 2 * E.card := by
  classical
  have hi : ∀ x ∈ A, x.2 ∈ E.image (fun n => N - n) := by
    intro x hx
    refine mem_image.mpr ⟨N - x.2, hcomp x hx, ?_⟩
    exact Nat.sub_sub_self (atom_data (hA hx)).1
  exact (card_le_indices hN he hk hD hA hi).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast card_image_le (s := E) (f := fun n => N - n))
      (by positivity))

theorem divisorBad_bound {N : ℕ} {k : ℝ} {D : Finset (ℕ × ℕ)}
    (hN : 4 ≤ N) (he : Even N) (hk : 0 < k) (hD : PairDomain N k D) :
    ((divisorBad N D).card : ℝ) ≤ 1 / k ^ 2 * (sqrt N + 1) := by
  classical
  have hc : ((divisorBad N D).card : ℝ) ≤ 1 / k ^ 2 * N.primeFactors.card := by
    apply card_le_indices hN he hk hD (filter_subset _ _)
    intro x hx
    obtain ⟨hx, hd⟩ := mem_filter.mp hx
    exact Nat.mem_primeFactors.mpr ⟨(atom_data hx).2.1, hd, by omega⟩
  exact hc.trans (mul_le_mul_of_nonneg_left (primeFactors_card_le_sqrt_add_one N) (by positivity))

theorem squareBad_bound {N : ℕ} {k : ℝ} {D : Finset (ℕ × ℕ)}
    (hN : 4 ≤ N) (he : Even N) (hk : 0 < k) (hD : PairDomain N k D)
    (hcut : 2 ≤ (N : ℝ) ^ k) :
    ((squareBad N D).card : ℝ) ≤ 2 / k ^ 2 * (N : ℝ) ^ (1 - k) := by
  classical
  have hc : ((squareBad N D).card : ℝ) ≤
      1 / k ^ 2 * (largePrimeSquareExceptions N ((N : ℝ) ^ k)).card := by
    apply card_le_complements hN he hk hD (filter_subset _ _)
    intro x hx
    obtain ⟨hx, hs⟩ := mem_filter.mp hx
    obtain ⟨hpN, hp, _⟩ := atom_data hx
    obtain ⟨ha, _, hka, _, _⟩ := hD x.1 (mem_atoms.mp hx).1
    exact mem_largePrimeSquareExceptions.mpr
      ⟨complement_pos_of_even hN he hpN hp, Nat.sub_le _ _, x.1.1, ha, hka, hs⟩
  have hp := mul_le_mul_of_nonneg_left
    (largePrimeSquareExceptions_card_le_rpow (by omega : 0 < N) hcut)
    (by positivity : 0 ≤ 1 / k ^ 2)
  calc
    _ ≤ 1 / k ^ 2 * (2 * (N : ℝ) ^ (1 - k)) := hc.trans hp
    _ = _ := by ring

theorem unit_complement_bound {N : ℕ} {k : ℝ} {D : Finset (ℕ × ℕ)}
    (hN : 0 < N) (hD : PairDomain N k D) {x : NinthLabel}
    (hx : x ∈ unitBad N D) : (N - x.2 : ℕ) ≤ (N : ℝ) ^ (1 - k) := by
  classical
  obtain ⟨hx, hu⟩ := mem_filter.mp hx
  obtain ⟨_, hb, hka, hab, hgeom⟩ := hD x.1 (mem_atoms.mp hx).1
  have hd := (atom_data hx).2.2
  have hmul : N - x.2 = x.1.1 * x.1.2 := by
    rw [← Nat.mul_div_cancel' hd, hu, mul_one]
  have hkb : (N : ℝ) ^ k ≤ x.1.2 := hka.trans (by exact_mod_cast hab.le)
  have hprod : (x.1.1 * x.1.2 : ℕ) * (N : ℝ) ^ k ≤ N := by
    calc
      _ ≤ (x.1.1 : ℝ) * x.1.2 * x.1.2 := by
        push_cast
        exact mul_le_mul_of_nonneg_left hkb (by positivity)
      _ = (x.1.1 * x.1.2 ^ 2 : ℕ) := by push_cast; ring
      _ ≤ N := by exact_mod_cast hgeom.le
  rw [hmul, rpow_sub (by positivity : (0 : ℝ) < N), rpow_one]
  exact (le_div_iff₀ (rpow_pos_of_pos (by positivity) _)).mpr hprod

theorem unitBad_bound {N : ℕ} {k : ℝ} {D : Finset (ℕ × ℕ)}
    (hN : 4 ≤ N) (he : Even N) (hk : 0 < k) (hD : PairDomain N k D) :
    ((unitBad N D).card : ℝ) ≤ 1 / k ^ 2 * (N : ℝ) ^ (1 - k) := by
  classical
  let E := Ioc 0 ⌊(N : ℝ) ^ (1 - k)⌋₊
  have hc : ((unitBad N D).card : ℝ) ≤ 1 / k ^ 2 * E.card := by
    apply card_le_complements hN he hk hD (filter_subset _ _)
    intro x hx
    have ha := (mem_filter.mp hx).1
    obtain ⟨hpN, hp, _⟩ := atom_data ha
    exact mem_Ioc.mpr ⟨complement_pos_of_even hN he hpN hp,
      Nat.le_floor (unit_complement_bound (by omega) hD hx)⟩
  have hE : (E.card : ℝ) ≤ (N : ℝ) ^ (1 - k) := by
    simpa [E] using (Nat.floor_le (by positivity : 0 ≤ (N : ℝ) ^ (1 - k)))
  exact hc.trans (mul_le_mul_of_nonneg_left hE (by positivity))

end Wu2008DoubleSieve.SeventhEighth
