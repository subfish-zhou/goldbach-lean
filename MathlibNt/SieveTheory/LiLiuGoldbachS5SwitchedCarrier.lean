import MathlibNt.SieveTheory.LiLiuGoldbachS5Cofactor
import MathlibNt.SieveTheory.LiLiuGoldbachS5CarrierGeometry

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachS5SwitchedCarrier (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- The literal closed S5 sum, retaining both the pair and the original integer. -/
noncomputable def goldbachS5ActualAtoms (N : ℕ) (eps : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachC9Pairs N).sigma fun rs =>
    (goldbachDifferenceCarrier N eps).filter
      (literalHPoint (N * rs.1) (goldbachC9Prod rs) rs.2)

theorem mem_goldbachS5ActualAtoms_iff {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachS5ActualAtoms N eps ↔
      x.1 ∈ goldbachC9Pairs N ∧ x.2 ∈ goldbachDifferenceCarrier N eps ∧
        literalHPoint (N * x.1.1) (goldbachC9Prod x.1) x.1.2 x.2 := by
  simp [goldbachS5ActualAtoms]

theorem goldbachS5Closed_eq_card_actualAtoms (N : ℕ) (eps : ℝ) :
    goldbachS5Closed (goldbachDifferenceCarrier N eps) N
      ((N : ℝ) ^ ((4 : ℝ) / 53)) ((N : ℝ) ^ ((1 : ℝ) / 3)) =
        ((goldbachS5ActualAtoms N eps).card : ℤ) := by
  simp [goldbachS5Closed, goldbachS5ActualAtoms, goldbachC9Pairs,
    goldbachC9Prod, goldbachC8Prod, literalH]
  rfl

noncomputable def goldbachS5BadAtoms (N : ℕ) (eps : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachS5ActualAtoms N eps).filter fun x => ¬Nat.Coprime x.2 N

noncomputable def goldbachS5GoodAtoms (N : ℕ) (eps : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachS5ActualAtoms N eps).filter fun x => Nat.Coprime x.2 N

noncomputable def goldbachS5SquareAtoms (N : ℕ) (eps : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachS5GoodAtoms N eps).filter fun x => x.1.1 ^ 2 ∣ x.2

noncomputable def goldbachS5GoodNonsquareAtoms (N : ℕ) (eps : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachS5GoodAtoms N eps).filter fun x => ¬x.1.1 ^ 2 ∣ x.2

/-- A set of integers, not a sum over square witnesses or a labelled atom count. -/
noncomputable def goldbachS5SquareSet (N : ℕ) : Finset ℕ :=
  (range N).filter fun n => 0 < n ∧
    ∃ r : ℕ, r.Prime ∧ (N : ℝ) ^ ((4 : ℝ) / 53) ≤ (r : ℝ) ∧ r ^ 2 ∣ n

theorem mem_goldbachS5SquareSet_iff {N n : ℕ} :
    n ∈ goldbachS5SquareSet N ↔
      0 < n ∧ n < N ∧
        ∃ r : ℕ, r.Prime ∧ (N : ℝ) ^ ((4 : ℝ) / 53) ≤ (r : ℝ) ∧ r ^ 2 ∣ n := by
  simp only [goldbachS5SquareSet, Finset.mem_filter, Finset.mem_range]
  tauto

noncomputable def goldbachS5SquareCount (N : ℕ) : ℤ :=
  (goldbachS5SquareSet N).card

def goldbachS5Cofactor (x : Σ _rs : ℕ × ℕ, ℕ) : ℕ :=
  x.2 / goldbachC9Prod x.1

theorem goldbachS5ActualAtom_factorization {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (hx : x ∈ goldbachS5ActualAtoms N eps) :
    x.2 = goldbachC9Prod x.1 * goldbachS5Cofactor x :=
  (Nat.mul_div_cancel' (mem_goldbachS5ActualAtoms_iff.mp hx).2.2.1).symm

theorem goldbachS5Cofactor_prime {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (hN : 2 ≤ N) (heps : 0 < eps)
    (hcut : (N : ℝ) ^ ((2 : ℝ) / 3) ≤ eps * N)
    (hx : x ∈ goldbachS5GoodNonsquareAtoms N eps) :
    (goldbachS5Cofactor x).Prime := by
  obtain ⟨hx, hnonsq⟩ := Finset.mem_filter.mp hx
  obtain ⟨ha, hcop⟩ := Finset.mem_filter.mp hx
  obtain ⟨hrs, hn, hpoint⟩ := mem_goldbachS5ActualAtoms_iff.mp ha
  exact (goldbachS5Closed_cofactor_prime_or_square hN heps hcut hrs hn hcop hpoint).resolve_right
    hnonsq

/-- The full prime-cofactor prefix: no order or coprimality condition is imposed on q. -/
noncomputable def goldbachB9PlusAtoms (N : ℕ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachC9Pairs N).sigma fun rs =>
    (range (N + 1)).filter fun q => q.Prime ∧ goldbachC9Prod rs * q < N

theorem mem_goldbachB9PlusAtoms_iff {N : ℕ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachB9PlusAtoms N ↔
      x.1 ∈ goldbachC9Pairs N ∧ x.2.Prime ∧ goldbachC9Prod x.1 * x.2 < N := by
  simp only [goldbachB9PlusAtoms, Finset.mem_sigma, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hrs, _, hq⟩
    exact ⟨hrs, hq⟩
  · rintro ⟨hrs, hp, hprod⟩
    have hqle := Nat.le_mul_of_pos_left x.2 (goldbachC9Prod_pos hrs)
    exact ⟨hrs, by omega, hp, hprod⟩

def goldbachB9PlusOutput (N : ℕ) (x : Σ _rs : ℕ × ℕ, ℕ) : ℕ :=
  N - goldbachC9Prod x.1 * x.2

noncomputable def goldbachB9PlusSiftedAtoms (N : ℕ) (Z : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachB9PlusAtoms N).filter fun x => literalHPoint N 1 Z (goldbachB9PlusOutput N x)

theorem mem_goldbachB9PlusSiftedAtoms_iff {N : ℕ} {Z : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachB9PlusSiftedAtoms N Z ↔
      x ∈ goldbachB9PlusAtoms N ∧ SurvivesSieve N Z (goldbachB9PlusOutput N x) := by
  simp [goldbachB9PlusSiftedAtoms, literalHPoint]

theorem goldbachB9PlusSiftedAtoms_eq_coprime_filter (N : ℕ) (Z : ℝ) :
    goldbachB9PlusSiftedAtoms N Z =
      (goldbachB9PlusAtoms N).filter
        fun x => Nat.Coprime (goldbachB10ProdPrimes N Z) (goldbachB9PlusOutput N x) := by
  ext x
  simp [goldbachB9PlusSiftedAtoms, goldbachB10_coprime_prodPrimes_iff_literalHPoint]

noncomputable def goldbachB9PlusPrimeAtoms (N : ℕ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachB9PlusAtoms N).filter fun x => (goldbachB9PlusOutput N x).Prime

noncomputable def goldbachB9PlusOutputFiber (N p : ℕ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachB9PlusAtoms N).filter fun x => goldbachB9PlusOutput N x = p

def goldbachS5Switch (x : Σ _rs : ℕ × ℕ, ℕ) : Σ _rs : ℕ × ℕ, ℕ :=
  ⟨x.1, goldbachS5Cofactor x⟩

theorem goldbachS5Switch_output {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (hx : x ∈ goldbachS5ActualAtoms N eps) :
    goldbachB9PlusOutput N (goldbachS5Switch x) = N - x.2 := by
  simpa [goldbachB9PlusOutput, goldbachS5Switch] using
    congrArg (fun n => N - n) (goldbachS5ActualAtom_factorization hx).symm

theorem goldbachS5Switch_injOn {N : ℕ} {eps : ℝ} :
    Set.InjOn goldbachS5Switch (goldbachS5ActualAtoms N eps) := by
  intro x hx y hy hxy
  have hpair : x.1 = y.1 := by
    simpa [goldbachS5Switch] using congrArg Sigma.fst hxy
  have hq : goldbachS5Cofactor x = goldbachS5Cofactor y := by
    simpa [goldbachS5Switch] using congrArg Sigma.snd hxy
  have hn : x.2 = y.2 := by
    rw [goldbachS5ActualAtom_factorization hx, goldbachS5ActualAtom_factorization hy,
      hpair, hq]
  exact Sigma.ext hpair (heq_of_eq hn)

theorem goldbachS5Switch_mem_primeAtoms {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (hN : 2 ≤ N) (heps : 0 < eps)
    (hcut : (N : ℝ) ^ ((2 : ℝ) / 3) ≤ eps * N)
    (hx : x ∈ goldbachS5GoodNonsquareAtoms N eps) :
    goldbachS5Switch x ∈ goldbachB9PlusPrimeAtoms N ∧
      eps * N < (goldbachC9Prod x.1 * goldbachS5Cofactor x : ℕ) := by
  have ha := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  obtain ⟨hrs, hn, _⟩ := mem_goldbachS5ActualAtoms_iff.mp ha
  have hb := goldbachG10DifferenceCarrier_bounds heps hn
  have heq := goldbachS5ActualAtom_factorization ha
  have hmem : goldbachS5Switch x ∈ goldbachB9PlusAtoms N :=
    mem_goldbachB9PlusAtoms_iff.mpr
      ⟨hrs, goldbachS5Cofactor_prime hN heps hcut hx, heq ▸ hb.2.1⟩
  have hout : (goldbachB9PlusOutput N (goldbachS5Switch x)).Prime := by
    rw [goldbachS5Switch_output ha]
    obtain ⟨p, hp, _, hnp⟩ := goldbachDifferenceCarrier_prime_data heps hn
    have hpN : p ≤ N := by omega
    simpa [hnp, Nat.sub_sub_self hpN] using hp
  exact ⟨Finset.mem_filter.mpr ⟨hmem, hout⟩, by simpa [← heq] using hb.2.2⟩

theorem goldbachS5GoodNonsquareAtoms_outputFiber_card_le {N p : ℕ} {eps : ℝ}
    (hN : 2 ≤ N) (heps : 0 < eps)
    (hcut : (N : ℝ) ^ ((2 : ℝ) / 3) ≤ eps * N) :
    ((goldbachS5GoodNonsquareAtoms N eps).filter fun x => N - x.2 = p).card ≤
      ((goldbachB9PlusPrimeAtoms N).filter fun x => goldbachB9PlusOutput N x = p).card := by
  apply Finset.card_le_card_of_injOn goldbachS5Switch
  · intro x hx
    obtain ⟨hx, hp⟩ := Finset.mem_filter.mp hx
    have ha := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
    exact Finset.mem_filter.mpr
      ⟨(goldbachS5Switch_mem_primeAtoms hN heps hcut hx).1,
        (goldbachS5Switch_output ha).trans hp⟩
  · intro x hx y hy hxy
    exact goldbachS5Switch_injOn
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).1
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1).1 hxy

private theorem S5_card_le_mul_of_fibers {α : Type*} [DecidableEq α]
    (A : Finset α) (T : Finset ℕ) (f : α → ℕ) (k : ℕ)
    (hmaps : ∀ x ∈ A, f x ∈ T)
    (hfiber : ∀ p ∈ T, (A.filter fun x => f x = p).card ≤ k) :
    A.card ≤ T.card * k := by
  have heq : (∑ p ∈ T, (A.filter fun x => f x = p).card) = A.card := by
    have hfilter : A.filter (fun x => f x ∈ T) = A := Finset.filter_eq_self.mpr hmaps
    simpa [hfilter] using Finset.sum_fiberwise_eq_sum_filter A T f (fun _ => (1 : ℕ))
  calc
    A.card = ∑ p ∈ T, (A.filter fun x => f x = p).card := heq.symm
    _ ≤ ∑ _p ∈ T, k := Finset.sum_le_sum hfiber
    _ = T.card * k := by simp

theorem goldbachS5ActualAtoms_fiber_card_le_fourHundred {N n : ℕ} {eps : ℝ}
    (hn1 : 1 ≤ n) (hnN : n < N) :
    ((goldbachS5ActualAtoms N eps).filter fun x => x.2 = n).card ≤ 400 := by
  let D := (goldbachC9Pairs N).filter fun rs => goldbachC9Prod rs ∣ n
  have hmaps : Set.MapsTo (fun x : Σ _rs : ℕ × ℕ, ℕ => x.1)
      ((goldbachS5ActualAtoms N eps).filter fun x => x.2 = n) D := by
    intro x hx
    obtain ⟨hx, hxn⟩ := Finset.mem_filter.mp hx
    obtain ⟨hrs, _, hpoint⟩ := mem_goldbachS5ActualAtoms_iff.mp hx
    exact Finset.mem_filter.mpr ⟨hrs, hxn ▸ hpoint.1⟩
  have hinj : Set.InjOn (fun x : Σ _rs : ℕ × ℕ, ℕ => x.1)
      ((goldbachS5ActualAtoms N eps).filter fun x => x.2 = n) := by
    intro x hx y hy hxy
    exact Sigma.ext hxy (heq_of_eq
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm))
  exact (Finset.card_le_card_of_injOn _ hmaps hinj).trans
    (goldbachC9Pair_dvdFiber_card_le_fourHundred hn1 hnN)

theorem goldbachS5BadAtoms_card_le {N : ℕ} {eps : ℝ} (heps : 0 < eps) :
    ((goldbachS5BadAtoms N eps).card : ℤ) ≤
      400 * goldbachBadCount (goldbachDifferenceCarrier N eps) N := by
  let T := (goldbachDifferenceCarrier N eps).filter fun n => ¬Nat.Coprime n N
  have hmaps : ∀ x ∈ goldbachS5BadAtoms N eps, x.2 ∈ T := by
    intro x hx
    obtain ⟨ha, hbad⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(mem_goldbachS5ActualAtoms_iff.mp ha).2.1, hbad⟩
  have hfiber : ∀ n ∈ T,
      ((goldbachS5BadAtoms N eps).filter fun x => x.2 = n).card ≤ 400 := by
    intro n hn
    have hb := goldbachG10DifferenceCarrier_bounds heps (Finset.mem_filter.mp hn).1
    have hsub : ((goldbachS5BadAtoms N eps).filter fun x => x.2 = n) ⊆
        ((goldbachS5ActualAtoms N eps).filter fun x => x.2 = n) := by
      intro x hx
      obtain ⟨hx, heq⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, heq⟩
    exact (Finset.card_le_card hsub).trans
      (goldbachS5ActualAtoms_fiber_card_le_fourHundred hb.1 hb.2.1)
  have h := S5_card_le_mul_of_fibers (goldbachS5BadAtoms N eps) T
    (fun x => x.2) 400 hmaps hfiber
  unfold goldbachBadCount
  exact_mod_cast (by simpa [T, mul_comm] using h :
    (goldbachS5BadAtoms N eps).card ≤
      400 * ((goldbachDifferenceCarrier N eps).filter fun n => ¬Nat.Coprime n N).card)

theorem goldbachS5SquareAtoms_card_le {N : ℕ} {eps : ℝ} (heps : 0 < eps) :
    ((goldbachS5SquareAtoms N eps).card : ℤ) ≤ 400 * goldbachS5SquareCount N := by
  have hmaps : ∀ x ∈ goldbachS5SquareAtoms N eps, x.2 ∈ goldbachS5SquareSet N := by
    intro x hx
    obtain ⟨hx, hsq⟩ := Finset.mem_filter.mp hx
    have ha := (Finset.mem_filter.mp hx).1
    obtain ⟨hrs, hn, _⟩ := mem_goldbachS5ActualAtoms_iff.mp ha
    have hb := goldbachG10DifferenceCarrier_bounds heps hn
    have hp := mem_goldbachC9Pairs_iff.mp hrs
    exact mem_goldbachS5SquareSet_iff.mpr
      ⟨by omega, hb.2.1, x.1.1, hp.1, hp.2.2.2.1, hsq⟩
  have hfiber : ∀ n ∈ goldbachS5SquareSet N,
      ((goldbachS5SquareAtoms N eps).filter fun x => x.2 = n).card ≤ 400 := by
    intro n hn
    obtain ⟨hn0, hnN, _⟩ := mem_goldbachS5SquareSet_iff.mp hn
    have hsub : ((goldbachS5SquareAtoms N eps).filter fun x => x.2 = n) ⊆
        ((goldbachS5ActualAtoms N eps).filter fun x => x.2 = n) := by
      intro x hx
      obtain ⟨hx, heq⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1, heq⟩
    exact (Finset.card_le_card hsub).trans
      (goldbachS5ActualAtoms_fiber_card_le_fourHundred hn0 hnN)
  have h := S5_card_le_mul_of_fibers (goldbachS5SquareAtoms N eps)
    (goldbachS5SquareSet N) (fun x => x.2) 400 hmaps hfiber
  unfold goldbachS5SquareCount
  exact_mod_cast (by simpa [mul_comm] using h :
    (goldbachS5SquareAtoms N eps).card ≤ 400 * (goldbachS5SquareSet N).card)

theorem goldbachB9PlusOutputFiber_card_le_fourHundred (N p : ℕ) :
    (goldbachB9PlusOutputFiber N p).card ≤ 400 := by
  let A := goldbachB9PlusOutputFiber N p
  by_cases hempty : A = ∅
  · simp [A] at hempty
    simp [hempty]
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨hxB, hxp⟩ := Finset.mem_filter.mp hx
    obtain ⟨hrs, hq, hprod⟩ := mem_goldbachB9PlusAtoms_iff.mp hxB
    have hpos := Nat.mul_pos (goldbachC9Prod_pos hrs) hq.pos
    have hEq : goldbachC9Prod x.1 * x.2 = N - p := by
      dsimp [goldbachB9PlusOutput] at hxp
      omega
    have hn1 : 1 ≤ N - p := by omega
    have hnN : N - p < N := by omega
    let D := (goldbachC9Pairs N).filter fun rs => goldbachC9Prod rs ∣ N - p
    have heq : ∀ y ∈ A, goldbachC9Prod y.1 * y.2 = N - p := by
      intro y hy
      obtain ⟨hyB, hyp⟩ := Finset.mem_filter.mp hy
      have hylt := (mem_goldbachB9PlusAtoms_iff.mp hyB).2.2
      dsimp [goldbachB9PlusOutput] at hyp
      omega
    have hmaps : Set.MapsTo (fun y : Σ _rs : ℕ × ℕ, ℕ => y.1) A D := by
      intro y hy
      exact Finset.mem_filter.mpr
        ⟨(mem_goldbachB9PlusAtoms_iff.mp (Finset.mem_filter.mp hy).1).1,
          ⟨y.2, (heq y hy).symm⟩⟩
    have hinj : Set.InjOn (fun y : Σ _rs : ℕ × ℕ, ℕ => y.1) A := by
      intro y hy z hz hyz
      dsimp only at hyz
      have hprod := (heq y hy).trans (heq z hz).symm
      rw [← hyz] at hprod
      have hmpos := goldbachC9Prod_pos
        (mem_goldbachB9PlusAtoms_iff.mp (Finset.mem_filter.mp hy).1).1
      exact Sigma.ext hyz (heq_of_eq (Nat.mul_left_cancel hmpos hprod))
    exact (Finset.card_le_card_of_injOn _ hmaps hinj).trans
      (goldbachC9Pair_dvdFiber_card_le_fourHundred hn1 hnN)

theorem goldbachB9Plus_low_card_le (N : ℕ) {Z : ℝ} (hZ : 1 ≤ Z) :
    (((goldbachB9PlusAtoms N).filter
      fun x => (goldbachB9PlusOutput N x : ℝ) < Z).card : ℤ) ≤
        400 * (Nat.floor Z : ℤ) := by
  let A := (goldbachB9PlusAtoms N).filter fun x => (goldbachB9PlusOutput N x : ℝ) < Z
  let T := Finset.Icc 1 (Nat.floor Z)
  have hmaps : ∀ x ∈ A, goldbachB9PlusOutput N x ∈ T := by
    intro x hx
    obtain ⟨hxB, hlow⟩ := Finset.mem_filter.mp hx
    have hprod := (mem_goldbachB9PlusAtoms_iff.mp hxB).2.2
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · dsimp [goldbachB9PlusOutput]
      omega
    · exact (Nat.le_floor_iff (by linarith : 0 ≤ Z)).mpr hlow.le
  have hfiber : ∀ p ∈ T, (A.filter fun x => goldbachB9PlusOutput N x = p).card ≤ 400 := by
    intro p _
    have hsub : (A.filter fun x => goldbachB9PlusOutput N x = p) ⊆
        goldbachB9PlusOutputFiber N p := by
      intro x hx
      obtain ⟨hx, heq⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, heq⟩
    exact (Finset.card_le_card hsub).trans (goldbachB9PlusOutputFiber_card_le_fourHundred N p)
  have h := S5_card_le_mul_of_fibers A T (goldbachB9PlusOutput N) 400 hmaps hfiber
  have hcardT : T.card = Nat.floor Z := by simp [T, Nat.card_Icc]
  rw [hcardT] at h
  exact_mod_cast (by simpa [A, mul_comm] using h :
    ((goldbachB9PlusAtoms N).filter fun x => (goldbachB9PlusOutput N x : ℝ) < Z).card ≤
      400 * Nat.floor Z)

theorem goldbachB9Plus_highPrime_subset_sifted (N : ℕ) (Z : ℝ) :
    (goldbachB9PlusPrimeAtoms N).filter
      (fun x => Z ≤ (goldbachB9PlusOutput N x : ℝ)) ⊆ goldbachB9PlusSiftedAtoms N Z := by
  intro x hx
  obtain ⟨hx, hhigh⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxB, hp⟩ := Finset.mem_filter.mp hx
  apply mem_goldbachB9PlusSiftedAtoms_iff.mpr
  refine ⟨hxB, ?_⟩
  intro ell hell hd _
  have heq := (Nat.prime_dvd_prime_iff_eq hell hp).mp hd
  simpa [heq] using hhigh

theorem goldbachB9PlusPrimeAtoms_card_le_sifted (N : ℕ) {Z : ℝ} (hZ : 1 ≤ Z) :
    ((goldbachB9PlusPrimeAtoms N).card : ℤ) ≤
      ((goldbachB9PlusSiftedAtoms N Z).card : ℤ) + 400 * (Nat.floor Z : ℤ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (goldbachB9PlusPrimeAtoms N)
    (fun x => (goldbachB9PlusOutput N x : ℝ) < Z) (fun _ => (1 : ℤ))
  have hlowSub : ((goldbachB9PlusPrimeAtoms N).filter
      fun x => (goldbachB9PlusOutput N x : ℝ) < Z) ⊆
      ((goldbachB9PlusAtoms N).filter fun x => (goldbachB9PlusOutput N x : ℝ) < Z) := by
    intro x hx
    obtain ⟨hx, hlow⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hlow⟩
  have hlow : (((goldbachB9PlusPrimeAtoms N).filter
      fun x => (goldbachB9PlusOutput N x : ℝ) < Z).card : ℤ) ≤
      400 * (Nat.floor Z : ℤ) := by
    have hc : (((goldbachB9PlusPrimeAtoms N).filter
        fun x => (goldbachB9PlusOutput N x : ℝ) < Z).card : ℤ) ≤
        (((goldbachB9PlusAtoms N).filter
          fun x => (goldbachB9PlusOutput N x : ℝ) < Z).card : ℤ) := by
      exact_mod_cast Finset.card_le_card hlowSub
    exact hc.trans (goldbachB9Plus_low_card_le N hZ)
  have hhigh : (((goldbachB9PlusPrimeAtoms N).filter
      fun x => Z ≤ (goldbachB9PlusOutput N x : ℝ)).card : ℤ) ≤
      ((goldbachB9PlusSiftedAtoms N Z).card : ℤ) := by
    exact_mod_cast Finset.card_le_card (goldbachB9Plus_highPrime_subset_sifted N Z)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, not_lt] at hsplit
  omega

/-- All three losses count labelled fibers, with the square set left unpaid asymptotically. -/
theorem goldbachS5Closed_le_sifted_B9Plus {N : ℕ} {eps Z : ℝ}
    (hN : 2 ≤ N) (heps : 0 < eps)
    (hcut : (N : ℝ) ^ ((2 : ℝ) / 3) ≤ eps * N) (hZ : 1 ≤ Z) :
    goldbachS5Closed (goldbachDifferenceCarrier N eps) N
      ((N : ℝ) ^ ((4 : ℝ) / 53)) ((N : ℝ) ^ ((1 : ℝ) / 3)) ≤
        ((goldbachB9PlusSiftedAtoms N Z).card : ℤ) +
          400 * goldbachBadCount (goldbachDifferenceCarrier N eps) N +
            400 * goldbachS5SquareCount N + 400 * (Nat.floor Z : ℤ) := by
  have hgood : ((goldbachS5GoodNonsquareAtoms N eps).card : ℤ) ≤
      ((goldbachB9PlusPrimeAtoms N).card : ℤ) := by
    have hmaps : Set.MapsTo goldbachS5Switch (goldbachS5GoodNonsquareAtoms N eps)
        (goldbachB9PlusPrimeAtoms N) :=
      fun _ hx => (goldbachS5Switch_mem_primeAtoms hN heps hcut hx).1
    have hinj : Set.InjOn goldbachS5Switch (goldbachS5GoodNonsquareAtoms N eps) :=
      fun _ hx _ hy hxy => goldbachS5Switch_injOn
        (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
        (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1 hxy
    exact_mod_cast Finset.card_le_card_of_injOn _ hmaps hinj
  have hsplit : ((goldbachS5GoodAtoms N eps).card : ℤ) +
      ((goldbachS5BadAtoms N eps).card : ℤ) = ((goldbachS5ActualAtoms N eps).card : ℤ) := by
    simpa [goldbachS5GoodAtoms, goldbachS5BadAtoms] using
      Finset.sum_filter_add_sum_filter_not (goldbachS5ActualAtoms N eps)
        (fun x => Nat.Coprime x.2 N) (fun _ => (1 : ℤ))
  have hsquareSplit : ((goldbachS5SquareAtoms N eps).card : ℤ) +
      ((goldbachS5GoodNonsquareAtoms N eps).card : ℤ) =
        ((goldbachS5GoodAtoms N eps).card : ℤ) := by
    simpa [goldbachS5SquareAtoms, goldbachS5GoodNonsquareAtoms] using
      Finset.sum_filter_add_sum_filter_not (goldbachS5GoodAtoms N eps)
        (fun x => x.1.1 ^ 2 ∣ x.2) (fun _ => (1 : ℤ))
  have hbad := goldbachS5BadAtoms_card_le (N := N) heps
  have hsquare := goldbachS5SquareAtoms_card_le (N := N) heps
  have hprime := goldbachB9PlusPrimeAtoms_card_le_sifted N hZ
  rw [goldbachS5Closed_eq_card_actualAtoms]
  omega

theorem goldbachS5Closed_eventually_le_sifted_B9Plus :
    ∀ eps : ℝ, 0 < eps →
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ Z : ℝ, 1 ≤ Z →
        goldbachS5Closed (goldbachDifferenceCarrier N eps) N
          ((N : ℝ) ^ ((4 : ℝ) / 53)) ((N : ℝ) ^ ((1 : ℝ) / 3)) ≤
            ((goldbachB9PlusSiftedAtoms N Z).card : ℤ) +
              400 * goldbachBadCount (goldbachDifferenceCarrier N eps) N +
                400 * goldbachS5SquareCount N + 400 * (Nat.floor Z : ℤ) := by
  intro eps heps
  obtain ⟨N0, hN0, hcut⟩ := exists_goldbachS4_switch_threshold eps heps
  exact ⟨N0, hN0, fun N hN Z hZ =>
    goldbachS5Closed_le_sifted_B9Plus (hN0.trans hN) heps (hcut N hN) hZ⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig