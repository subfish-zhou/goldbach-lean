import MathlibNt.SieveTheory.LiLiuGoldbachS4CarrierGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachB10FibreSieve

open scoped BigOperators
open Finset Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachS4SwitchedCarrier (P : Prop) : Decidable P := Classical.propDecidable P

/-- The original integers are sifted with modulus `N*r`, before taking a quotient. -/
noncomputable def goldbachS4ActualAtoms (N : ℕ) (eps : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachS4Pairs N ((N : ℝ) ^ ((3 : ℝ) / 11))).sigma fun rs =>
    (goldbachDifferenceCarrier N eps).filter
      (literalHPoint (N * rs.1) (goldbachC8Prod rs) rs.2)

theorem mem_goldbachS4ActualAtoms_iff {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachS4ActualAtoms N eps ↔
      x.1 ∈ goldbachS4Pairs N ((N : ℝ) ^ ((3 : ℝ) / 11)) ∧
        x.2 ∈ goldbachDifferenceCarrier N eps ∧
          literalHPoint (N * x.1.1) (goldbachC8Prod x.1) x.1.2 x.2 := by
  simp [goldbachS4ActualAtoms]

theorem goldbachS4_eq_card_actualAtoms (N : ℕ) (eps : ℝ) :
    goldbachS4 (goldbachDifferenceCarrier N eps) N ((N : ℝ) ^ ((3 : ℝ) / 11)) =
      ((goldbachS4ActualAtoms N eps).card : ℤ) := by
  simp [goldbachS4, goldbachS4ActualAtoms, goldbachC8Prod, literalH]
  rfl

noncomputable def goldbachS4BadAtoms (N : ℕ) (eps : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachS4ActualAtoms N eps).filter fun x => ¬Nat.Coprime x.2 N

/-- Nonbad means only coprimality of the original integer with `N`. -/
noncomputable def goldbachS4GoodAtoms (N : ℕ) (eps : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachS4ActualAtoms N eps).filter fun x => Nat.Coprime x.2 N

def goldbachS4Cofactor (x : Σ _rs : ℕ × ℕ, ℕ) : ℕ :=
  x.2 / goldbachC8Prod x.1

theorem goldbachS4ActualAtom_factorization {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (hx : x ∈ goldbachS4ActualAtoms N eps) :
    x.2 = goldbachC8Prod x.1 * goldbachS4Cofactor x :=
  (Nat.mul_div_cancel' (mem_goldbachS4ActualAtoms_iff.mp hx).2.2.1).symm

theorem goldbachS4Cofactor_two_le {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (hN : 2 ≤ N) (heps : 0 < eps)
    (hcut : (N : ℝ) ^ ((2 : ℝ) / 3) ≤ eps * N)
    (hx : x ∈ goldbachS4ActualAtoms N eps) :
    2 ≤ goldbachS4Cofactor x := by
  obtain ⟨hrs, hn, _⟩ := mem_goldbachS4ActualAtoms_iff.mp hx
  have hb := goldbachG10DifferenceCarrier_bounds heps hn
  have hm := goldbachC8Prod_le_two_thirds hN hrs
  have hmn : goldbachC8Prod x.1 < x.2 := by
    exact_mod_cast (hm.trans hcut).trans_lt hb.2.2
  have heq := goldbachS4ActualAtom_factorization hx
  nlinarith

theorem goldbachS4Cofactor_primeDivisor_ge {N ell : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (hx : x ∈ goldbachS4GoodAtoms N eps)
    (hell : ell.Prime) (hd : ell ∣ goldbachS4Cofactor x) :
    (N : ℝ) ^ ((3 : ℝ) / 11) ≤ (ell : ℝ) := by
  obtain ⟨hx, hcop⟩ := Finset.mem_filter.mp hx
  obtain ⟨hrs, _, hpoint⟩ := mem_goldbachS4ActualAtoms_iff.mp hx
  have h := mem_goldbachS4Pairs_iff.mp hrs
  by_cases heq : ell = x.1.1
  · simpa [heq] using h.2.2.2.1
  · have hdn : ell ∣ x.2 := by
      rw [goldbachS4ActualAtom_factorization hx]
      exact dvd_mul_of_dvd_right hd _
    have hnotN : ¬ell ∣ N := prime_not_dvd_of_coprime hcop hell hdn
    have hnotr : ¬ell ∣ x.1.1 :=
      fun hr => heq ((Nat.prime_dvd_prime_iff_eq hell h.1).mp hr)
    have hnot : ¬ell ∣ N * x.1.1 :=
      fun hdNr => (hell.dvd_mul.mp hdNr).elim hnotN hnotr
    exact h.2.2.2.1.trans
      ((by exact_mod_cast h.2.2.2.2.1 : (x.1.1 : ℝ) ≤ x.1.2).trans
        (hpoint.2 ell hell hdn hnot))

/-- Four large factors cannot fit below `N`; repeated prime factors are retained. -/
theorem goldbachS4Cofactor_prime {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (hN : 2 ≤ N) (heps : 0 < eps)
    (hcut : (N : ℝ) ^ ((2 : ℝ) / 3) ≤ eps * N)
    (hx : x ∈ goldbachS4GoodAtoms N eps) :
    (goldbachS4Cofactor x).Prime := by
  have ha := (Finset.mem_filter.mp hx).1
  obtain ⟨hrs, hn, _⟩ := mem_goldbachS4ActualAtoms_iff.mp ha
  have hq2 := goldbachS4Cofactor_two_le hN heps hcut ha
  have hb := goldbachG10DifferenceCarrier_bounds heps hn
  have heq := goldbachS4ActualAtom_factorization ha
  by_contra hprime
  have hfac := Nat.minFac_prime (by omega : goldbachS4Cofactor x ≠ 1)
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < goldbachS4Cofactor x) hprime
  have hlarge := goldbachS4Cofactor_primeDivisor_ge hx hfac (Nat.minFac_dvd _)
  let u : ℝ := (N : ℝ) ^ ((3 : ℝ) / 11)
  have hu : 0 ≤ u := Real.rpow_nonneg (by positivity) _
  have hq : u ^ 2 ≤ (goldbachS4Cofactor x : ℝ) := by
    have hsqR : (Nat.minFac (goldbachS4Cofactor x) : ℝ) ^ 2 ≤
        (goldbachS4Cofactor x : ℝ) := by exact_mod_cast hsq
    have hpow : u ^ 2 ≤ (Nat.minFac (goldbachS4Cofactor x) : ℝ) ^ 2 := by
      gcongr
    exact hpow.trans hsqR
  have hm : u ^ 2 ≤ (goldbachC8Prod x.1 : ℝ) := by
    have h := (goldbachC8Prod_support_bounds hN hrs).1
    have hu2 : u ^ 2 = (N : ℝ) ^ ((6 : ℝ) / 11) := by
      dsimp [u]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
      norm_num
    rwa [hu2]
  have hfour : u ^ 4 ≤ (x.2 : ℝ) := by
    calc
      u ^ 4 = u ^ 2 * u ^ 2 := by ring
      _ ≤ (goldbachC8Prod x.1 : ℝ) * (goldbachS4Cofactor x : ℝ) :=
        mul_le_mul hm hq (sq_nonneg u) (by positivity)
      _ = (x.2 : ℝ) := by exact_mod_cast heq.symm
  have hNlt : (N : ℝ) < u ^ 4 := goldbachS4Cutoff_fourth_gt hN
  have hnN : (x.2 : ℝ) < N := by exact_mod_cast hb.2.1
  linarith

/-- One full prefix, without an epsilon lower endpoint or restrictions on `q` relative to `r,s`. -/
noncomputable def goldbachB8PlusAtoms (N : ℕ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachS4Pairs N ((N : ℝ) ^ ((3 : ℝ) / 11))).sigma fun rs =>
    (range (N + 1)).filter fun q => q.Prime ∧ goldbachC8Prod rs * q < N

theorem mem_goldbachB8PlusAtoms_iff {N : ℕ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachB8PlusAtoms N ↔
      x.1 ∈ goldbachS4Pairs N ((N : ℝ) ^ ((3 : ℝ) / 11)) ∧
        x.2.Prime ∧ goldbachC8Prod x.1 * x.2 < N := by
  simp only [goldbachB8PlusAtoms, Finset.mem_sigma, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hrs, _, hq⟩
    exact ⟨hrs, hq⟩
  · rintro ⟨hrs, hp, hprod⟩
    have hqle := Nat.le_mul_of_pos_left x.2 (goldbachC8Prod_pos hrs)
    exact ⟨hrs, by omega, hp, hprod⟩

def goldbachB8PlusOutput (N : ℕ) (x : Σ _rs : ℕ × ℕ, ℕ) : ℕ :=
  N - goldbachC8Prod x.1 * x.2

noncomputable def goldbachB8PlusSiftedAtoms (N : ℕ) (Z : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachB8PlusAtoms N).filter fun x => literalHPoint N 1 Z (goldbachB8PlusOutput N x)

theorem mem_goldbachB8PlusSiftedAtoms_iff {N : ℕ} {Z : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachB8PlusSiftedAtoms N Z ↔
      x ∈ goldbachB8PlusAtoms N ∧ SurvivesSieve N Z (goldbachB8PlusOutput N x) := by
  simp [goldbachB8PlusSiftedAtoms, literalHPoint]

theorem goldbachB8PlusSiftedAtoms_eq_coprime_filter (N : ℕ) (Z : ℝ) :
    goldbachB8PlusSiftedAtoms N Z =
      (goldbachB8PlusAtoms N).filter
        fun x => Nat.Coprime (goldbachB10ProdPrimes N Z) (goldbachB8PlusOutput N x) := by
  ext x
  simp [goldbachB8PlusSiftedAtoms, goldbachB10_coprime_prodPrimes_iff_literalHPoint]

noncomputable def goldbachB8PlusPrimeAtoms (N : ℕ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachB8PlusAtoms N).filter fun x => (goldbachB8PlusOutput N x).Prime

noncomputable def goldbachB8PlusOutputFiber (N p : ℕ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachB8PlusAtoms N).filter fun x => goldbachB8PlusOutput N x = p

def goldbachS4Switch (x : Σ _rs : ℕ × ℕ, ℕ) : Σ _rs : ℕ × ℕ, ℕ :=
  ⟨x.1, goldbachS4Cofactor x⟩

theorem goldbachS4Switch_output {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (hx : x ∈ goldbachS4ActualAtoms N eps) :
    goldbachB8PlusOutput N (goldbachS4Switch x) = N - x.2 := by
  simpa [goldbachB8PlusOutput, goldbachS4Switch] using
    congrArg (fun n => N - n) (goldbachS4ActualAtom_factorization hx).symm

theorem goldbachS4Switch_injOn {N : ℕ} {eps : ℝ} :
    Set.InjOn goldbachS4Switch (goldbachS4ActualAtoms N eps) := by
  intro x hx y hy hxy
  have hpair : x.1 = y.1 := by
    simpa [goldbachS4Switch] using congrArg Sigma.fst hxy
  have hq : goldbachS4Cofactor x = goldbachS4Cofactor y := by
    simpa [goldbachS4Switch] using congrArg Sigma.snd hxy
  have hn : x.2 = y.2 := by
    rw [goldbachS4ActualAtom_factorization hx, goldbachS4ActualAtom_factorization hy,
      hpair, hq]
  exact Sigma.ext hpair (heq_of_eq hn)

theorem goldbachS4Switch_mem_primeAtoms {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (hN : 2 ≤ N) (heps : 0 < eps)
    (hcut : (N : ℝ) ^ ((2 : ℝ) / 3) ≤ eps * N)
    (hx : x ∈ goldbachS4GoodAtoms N eps) :
    goldbachS4Switch x ∈ goldbachB8PlusPrimeAtoms N ∧
      eps * N < (goldbachC8Prod x.1 * goldbachS4Cofactor x : ℕ) := by
  have ha := (Finset.mem_filter.mp hx).1
  obtain ⟨hrs, hn, _⟩ := mem_goldbachS4ActualAtoms_iff.mp ha
  have hb := goldbachG10DifferenceCarrier_bounds heps hn
  have heq := goldbachS4ActualAtom_factorization ha
  have hmem : goldbachS4Switch x ∈ goldbachB8PlusAtoms N :=
    mem_goldbachB8PlusAtoms_iff.mpr
      ⟨hrs, goldbachS4Cofactor_prime hN heps hcut hx, heq ▸ hb.2.1⟩
  have hout : (goldbachB8PlusOutput N (goldbachS4Switch x)).Prime := by
    rw [goldbachS4Switch_output ha]
    obtain ⟨p, hp, _, hnp⟩ := goldbachDifferenceCarrier_prime_data heps hn
    have hpN : p ≤ N := by omega
    simpa [hnp, Nat.sub_sub_self hpN] using hp
  exact ⟨Finset.mem_filter.mpr ⟨hmem, hout⟩, by simpa [← heq] using hb.2.2⟩

private theorem S4_card_le_mul_of_fibers {α : Type*} [DecidableEq α]
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

theorem goldbachS4ActualAtoms_fiber_card_le_fourHundred {N n : ℕ} {eps : ℝ}
    (hn1 : 1 ≤ n) (hnN : n < N) :
    ((goldbachS4ActualAtoms N eps).filter fun x => x.2 = n).card ≤ 400 := by
  let D := (goldbachS4Pairs N ((N : ℝ) ^ ((3 : ℝ) / 11))).filter
    fun rs => goldbachC8Prod rs ∣ n
  have hmaps : Set.MapsTo (fun x : Σ _rs : ℕ × ℕ, ℕ => x.1)
      ((goldbachS4ActualAtoms N eps).filter fun x => x.2 = n) D := by
    intro x hx
    obtain ⟨hx, hxn⟩ := Finset.mem_filter.mp hx
    obtain ⟨hrs, _, hpoint⟩ := mem_goldbachS4ActualAtoms_iff.mp hx
    exact Finset.mem_filter.mpr ⟨hrs, hxn ▸ hpoint.1⟩
  have hinj : Set.InjOn (fun x : Σ _rs : ℕ × ℕ, ℕ => x.1)
      ((goldbachS4ActualAtoms N eps).filter fun x => x.2 = n) := by
    intro x hx y hy hxy
    exact Sigma.ext hxy (heq_of_eq
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm))
  exact (Finset.card_le_card_of_injOn _ hmaps hinj).trans
    (goldbachS4Pair_dvdFiber_card_le_fourHundred hn1 hnN)

theorem goldbachS4BadAtoms_card_le {N : ℕ} {eps : ℝ} (heps : 0 < eps) :
    ((goldbachS4BadAtoms N eps).card : ℤ) ≤
      400 * goldbachBadCount (goldbachDifferenceCarrier N eps) N := by
  let T := (goldbachDifferenceCarrier N eps).filter fun n => ¬Nat.Coprime n N
  have hmaps : ∀ x ∈ goldbachS4BadAtoms N eps, x.2 ∈ T := by
    intro x hx
    obtain ⟨ha, hbad⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(mem_goldbachS4ActualAtoms_iff.mp ha).2.1, hbad⟩
  have hfiber : ∀ n ∈ T,
      ((goldbachS4BadAtoms N eps).filter fun x => x.2 = n).card ≤ 400 := by
    intro n hn
    have hb := goldbachG10DifferenceCarrier_bounds heps (Finset.mem_filter.mp hn).1
    have hsub : ((goldbachS4BadAtoms N eps).filter fun x => x.2 = n) ⊆
        ((goldbachS4ActualAtoms N eps).filter fun x => x.2 = n) := by
      intro x hx
      obtain ⟨hx, heq⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, heq⟩
    exact (Finset.card_le_card hsub).trans
      (goldbachS4ActualAtoms_fiber_card_le_fourHundred hb.1 hb.2.1)
  have h := S4_card_le_mul_of_fibers (goldbachS4BadAtoms N eps) T
    (fun x => x.2) 400 hmaps hfiber
  unfold goldbachBadCount
  exact_mod_cast (by simpa [T, mul_comm] using h :
    (goldbachS4BadAtoms N eps).card ≤
      400 * ((goldbachDifferenceCarrier N eps).filter fun n => ¬Nat.Coprime n N).card)

theorem goldbachB8PlusOutputFiber_card_le_fourHundred (N p : ℕ) :
    (goldbachB8PlusOutputFiber N p).card ≤ 400 := by
  let A := goldbachB8PlusOutputFiber N p
  by_cases hempty : A = ∅
  · simp [A] at hempty
    simp [hempty]
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨hxB, hxp⟩ := Finset.mem_filter.mp hx
    obtain ⟨hrs, hq, hprod⟩ := mem_goldbachB8PlusAtoms_iff.mp hxB
    have hpos := Nat.mul_pos (goldbachC8Prod_pos hrs) hq.pos
    have hEq : goldbachC8Prod x.1 * x.2 = N - p := by
      dsimp [goldbachB8PlusOutput] at hxp
      omega
    have hn1 : 1 ≤ N - p := by omega
    have hnN : N - p < N := by omega
    let D := (goldbachS4Pairs N ((N : ℝ) ^ ((3 : ℝ) / 11))).filter
      fun rs => goldbachC8Prod rs ∣ N - p
    have heq : ∀ y ∈ A, goldbachC8Prod y.1 * y.2 = N - p := by
      intro y hy
      obtain ⟨hyB, hyp⟩ := Finset.mem_filter.mp hy
      have hylt := (mem_goldbachB8PlusAtoms_iff.mp hyB).2.2
      dsimp [goldbachB8PlusOutput] at hyp
      omega
    have hmaps : Set.MapsTo (fun y : Σ _rs : ℕ × ℕ, ℕ => y.1) A D := by
      intro y hy
      exact Finset.mem_filter.mpr
        ⟨(mem_goldbachB8PlusAtoms_iff.mp (Finset.mem_filter.mp hy).1).1,
          ⟨y.2, (heq y hy).symm⟩⟩
    have hinj : Set.InjOn (fun y : Σ _rs : ℕ × ℕ, ℕ => y.1) A := by
      intro y hy z hz hyz
      dsimp only at hyz
      have hprod := (heq y hy).trans (heq z hz).symm
      rw [← hyz] at hprod
      have hmpos := goldbachC8Prod_pos
        (mem_goldbachB8PlusAtoms_iff.mp (Finset.mem_filter.mp hy).1).1
      exact Sigma.ext hyz (heq_of_eq (Nat.mul_left_cancel hmpos hprod))
    exact (Finset.card_le_card_of_injOn _ hmaps hinj).trans
      (goldbachS4Pair_dvdFiber_card_le_fourHundred hn1 hnN)

theorem goldbachB8Plus_low_card_le (N : ℕ) {Z : ℝ} (hZ : 1 ≤ Z) :
    (((goldbachB8PlusAtoms N).filter
      fun x => (goldbachB8PlusOutput N x : ℝ) < Z).card : ℤ) ≤
        400 * (Nat.floor Z : ℤ) := by
  let A := (goldbachB8PlusAtoms N).filter fun x => (goldbachB8PlusOutput N x : ℝ) < Z
  let T := Finset.Icc 1 (Nat.floor Z)
  have hmaps : ∀ x ∈ A, goldbachB8PlusOutput N x ∈ T := by
    intro x hx
    obtain ⟨hxB, hlow⟩ := Finset.mem_filter.mp hx
    have hprod := (mem_goldbachB8PlusAtoms_iff.mp hxB).2.2
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · dsimp [goldbachB8PlusOutput]
      omega
    · exact (Nat.le_floor_iff (by linarith : 0 ≤ Z)).mpr hlow.le
  have hfiber : ∀ p ∈ T, (A.filter fun x => goldbachB8PlusOutput N x = p).card ≤ 400 := by
    intro p _
    have hsub : (A.filter fun x => goldbachB8PlusOutput N x = p) ⊆
        goldbachB8PlusOutputFiber N p := by
      intro x hx
      obtain ⟨hx, heq⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, heq⟩
    exact (Finset.card_le_card hsub).trans (goldbachB8PlusOutputFiber_card_le_fourHundred N p)
  have h := S4_card_le_mul_of_fibers A T (goldbachB8PlusOutput N) 400 hmaps hfiber
  have hcardT : T.card = Nat.floor Z := by simp [T, Nat.card_Icc]
  rw [hcardT] at h
  exact_mod_cast (by simpa [A, mul_comm] using h :
    ((goldbachB8PlusAtoms N).filter fun x => (goldbachB8PlusOutput N x : ℝ) < Z).card ≤
      400 * Nat.floor Z)

theorem goldbachB8Plus_highPrime_subset_sifted (N : ℕ) (Z : ℝ) :
    (goldbachB8PlusPrimeAtoms N).filter
      (fun x => Z ≤ (goldbachB8PlusOutput N x : ℝ)) ⊆ goldbachB8PlusSiftedAtoms N Z := by
  intro x hx
  obtain ⟨hx, hhigh⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxB, hp⟩ := Finset.mem_filter.mp hx
  apply mem_goldbachB8PlusSiftedAtoms_iff.mpr
  refine ⟨hxB, ?_⟩
  intro ell hell hd _
  have heq := (Nat.prime_dvd_prime_iff_eq hell hp).mp hd
  simpa [heq] using hhigh

theorem goldbachB8PlusPrimeAtoms_card_le_sifted (N : ℕ) {Z : ℝ} (hZ : 1 ≤ Z) :
    ((goldbachB8PlusPrimeAtoms N).card : ℤ) ≤
      ((goldbachB8PlusSiftedAtoms N Z).card : ℤ) + 400 * (Nat.floor Z : ℤ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (goldbachB8PlusPrimeAtoms N)
    (fun x => (goldbachB8PlusOutput N x : ℝ) < Z) (fun _ => (1 : ℤ))
  have hlowSub : ((goldbachB8PlusPrimeAtoms N).filter
      fun x => (goldbachB8PlusOutput N x : ℝ) < Z) ⊆
      ((goldbachB8PlusAtoms N).filter fun x => (goldbachB8PlusOutput N x : ℝ) < Z) := by
    intro x hx
    obtain ⟨hx, hlow⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hlow⟩
  have hlow : (((goldbachB8PlusPrimeAtoms N).filter
      fun x => (goldbachB8PlusOutput N x : ℝ) < Z).card : ℤ) ≤
      400 * (Nat.floor Z : ℤ) := by
    have hc : (((goldbachB8PlusPrimeAtoms N).filter
        fun x => (goldbachB8PlusOutput N x : ℝ) < Z).card : ℤ) ≤
        (((goldbachB8PlusAtoms N).filter
          fun x => (goldbachB8PlusOutput N x : ℝ) < Z).card : ℤ) := by
      exact_mod_cast Finset.card_le_card hlowSub
    exact hc.trans (goldbachB8Plus_low_card_le N hZ)
  have hhigh : (((goldbachB8PlusPrimeAtoms N).filter
      fun x => Z ≤ (goldbachB8PlusOutput N x : ℝ)).card : ℤ) ≤
      ((goldbachB8PlusSiftedAtoms N Z).card : ℤ) := by
    exact_mod_cast Finset.card_le_card (goldbachB8Plus_highPrime_subset_sifted N Z)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, not_lt] at hsplit
  omega

/-- The finite switch for the actual S4, with both labelled losses paid explicitly. -/
theorem goldbachS4_le_sifted_B8Plus {N : ℕ} {eps Z : ℝ}
    (hN : 2 ≤ N) (heps : 0 < eps)
    (hcut : (N : ℝ) ^ ((2 : ℝ) / 3) ≤ eps * N) (hZ : 1 ≤ Z) :
    goldbachS4 (goldbachDifferenceCarrier N eps) N ((N : ℝ) ^ ((3 : ℝ) / 11)) ≤
      ((goldbachB8PlusSiftedAtoms N Z).card : ℤ) +
        400 * goldbachBadCount (goldbachDifferenceCarrier N eps) N +
          400 * (Nat.floor Z : ℤ) := by
  have hgood : ((goldbachS4GoodAtoms N eps).card : ℤ) ≤
      ((goldbachB8PlusPrimeAtoms N).card : ℤ) := by
    have hmaps : Set.MapsTo goldbachS4Switch (goldbachS4GoodAtoms N eps)
        (goldbachB8PlusPrimeAtoms N) :=
      fun _ hx => (goldbachS4Switch_mem_primeAtoms hN heps hcut hx).1
    have hinj : Set.InjOn goldbachS4Switch (goldbachS4GoodAtoms N eps) :=
      fun _ hx _ hy hxy => goldbachS4Switch_injOn
        (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
    exact_mod_cast Finset.card_le_card_of_injOn _ hmaps hinj
  have hsplit : ((goldbachS4GoodAtoms N eps).card : ℤ) +
      ((goldbachS4BadAtoms N eps).card : ℤ) = ((goldbachS4ActualAtoms N eps).card : ℤ) := by
    simpa [goldbachS4GoodAtoms, goldbachS4BadAtoms] using
      Finset.sum_filter_add_sum_filter_not (goldbachS4ActualAtoms N eps)
        (fun x => Nat.Coprime x.2 N) (fun _ => (1 : ℤ))
  have hbad := goldbachS4BadAtoms_card_le (N := N) heps
  have hprime := goldbachB8PlusPrimeAtoms_card_le_sifted N hZ
  rw [goldbachS4_eq_card_actualAtoms]
  omega

theorem exists_goldbachS4_switch_threshold (eps : ℝ) (heps : 0 < eps) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (N : ℝ) ^ ((2 : ℝ) / 3) ≤ eps * N := by
  have hpow : ∀ᶠ N : ℕ in atTop, 1 ≤ eps * (N : ℝ) ^ ((1 : ℝ) / 3) :=
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop heps).eventually (eventually_ge_atTop 1)
  obtain ⟨K, hK⟩ := Filter.Eventually.exists_forall_of_atTop hpow
  refine ⟨max K 2, le_max_right _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_right K 2).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := mul_le_mul_of_nonneg_left (hK N ((le_max_left K 2).trans hN))
    (Real.rpow_nonneg hN0.le ((2 : ℝ) / 3))
  have hid : (N : ℝ) ^ ((2 : ℝ) / 3) * (eps * (N : ℝ) ^ ((1 : ℝ) / 3)) =
      eps * N := by
    rw [mul_left_comm, ← Real.rpow_add hN0]
    norm_num
  simpa only [mul_one, hid] using h

theorem goldbachS4_eventually_le_sifted_B8Plus :
    ∀ eps : ℝ, 0 < eps → eps < (2 : ℝ) / 15 →
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ Z : ℝ, 1 ≤ Z →
        goldbachS4 (goldbachDifferenceCarrier N eps) N ((N : ℝ) ^ ((3 : ℝ) / 11)) ≤
          ((goldbachB8PlusSiftedAtoms N Z).card : ℤ) +
            400 * goldbachBadCount (goldbachDifferenceCarrier N eps) N +
              400 * (Nat.floor Z : ℤ) := by
  intro eps heps _
  obtain ⟨N0, hN0, hcut⟩ := exists_goldbachS4_switch_threshold eps heps
  exact ⟨N0, hN0, fun N hN Z hZ =>
    goldbachS4_le_sifted_B8Plus (hN0.trans hN) heps (hcut N hN) hZ⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig