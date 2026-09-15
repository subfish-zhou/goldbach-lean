import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedTypeIIActualDecomposition
import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedArctanHyperbolicPrimitiveL1

/-!
# Exact rectangular sharp bridge for one Vaughan Type-II shell

This module only records a finite identity.  It does not claim any scalar
large-sieve closure.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Möbius coefficient, extended by zero away from one canonical `d`-block. -/
def vaughanTypeIIRectLeftCoeff (N u k : ℕ) (d : ℤ) : ℂ :=
  if d.toNat ∈ vaughanCanonicalDyadicBlock N u k then
    vaughanMoebiusCoeff d.toNat else 0

/-- The collected Mangoldt divisor coefficient on one canonical `e`-block. -/
def vaughanTypeIIRectRightCoeff (N v l : ℕ) (t : ℤ) : ℂ :=
  ∑ e ∈ vaughanCanonicalDyadicBlock N v l,
    if e ∣ t.toNat then vaughanMangoldtCoeff e else 0

/-- With production coefficient `b = 1`, the actual tensor fibre is exactly the
canonical-block divisor sum whenever the displayed product lies under the
hyperbolic cutoff. -/
theorem vaughanBilinearTensorCoeff_one_eq_rectRightCoeff
    (N v l y d : ℕ) (t : ℤ)
    (hd : 0 < d) (ht : 1 ≤ t) (hdt : (d : ℤ) * t ≤ y) :
    vaughanBilinearTensorCoeff vaughanMangoldtCoeff (fun _ => 1) y d
        (vaughanCanonicalDyadicBlock N v l) t =
      vaughanTypeIIRectRightCoeff N v l t := by
  rw [vaughanBilinearTensorCoeff_eq_fiber]
  · unfold vaughanTypeIIRectRightCoeff vaughanTensorFiber
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    have he0 : 0 < e := (mem_vaughanCanonicalDyadicBlock.mp he).1
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht
    have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
    by_cases het : e ∣ t.toNat
    · rw [if_pos het, if_pos]
      · simp
      · obtain ⟨m, hm⟩ := het
        have htNatPos : 0 < t.toNat := by
          rw [← Int.natCast_pos, htcast]
          omega
        have hm0 : 0 < m := by
          by_contra hm0
          simp only [not_lt, Nat.le_zero] at hm0
          subst m
          simp at hm htNatPos
          omega
        have hmet : ((e * m : ℕ) : ℤ) = t := by
          rw [← hm, htcast]
        refine ⟨m, Finset.mem_Icc.mpr ⟨hm0, ?_⟩, ?_⟩
        · apply (Nat.le_div_iff_mul_le (Nat.mul_pos hd he0)).2
          exact_mod_cast (show (m : ℤ) * ((d : ℤ) * e) ≤ y by
            calc
              (m : ℤ) * ((d : ℤ) * e) = (d : ℤ) * (e * m) := by ring
              _ = (d : ℤ) * t := by rw [← Nat.cast_mul, hmet]
              _ ≤ y := hdt)
        · exact hmet
    · rw [if_neg het, if_neg]
      rintro ⟨m, hm, hprod⟩
      apply het
      refine ⟨m, ?_⟩
      apply Int.ofNat_inj.mp
      rw [htcast]
      simpa using hprod.symm
  · intro e he
    exact (mem_vaughanCanonicalDyadicBlock.mp he).1

private theorem vaughanBilinearTensorCoeff_one_eq_ite_rectRightCoeff
    (N v l y d : ℕ) (t : ℤ) (hd : 0 < d) (ht : 1 ≤ t) :
    vaughanBilinearTensorCoeff vaughanMangoldtCoeff (fun _ => 1) y d
        (vaughanCanonicalDyadicBlock N v l) t =
      if (d : ℤ) * t ≤ y then vaughanTypeIIRectRightCoeff N v l t else 0 := by
  by_cases hdt : (d : ℤ) * t ≤ y
  · rw [if_pos hdt]
    exact vaughanBilinearTensorCoeff_one_eq_rectRightCoeff N v l y d t hd ht hdt
  · rw [if_neg hdt]
    unfold vaughanBilinearTensorCoeff
    apply Finset.sum_eq_zero
    intro e he
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    intro hem
    apply hdt
    have he0 : 0 < e := (mem_vaughanCanonicalDyadicBlock.mp he).1
    have hde : 0 < d * e := Nat.mul_pos hd he0
    have hprod : d * e * m ≤ y := by
      simpa [mul_comm] using
        (Nat.le_div_iff_mul_le hde).mp (Finset.mem_Icc.mp hm).2
    exact_mod_cast (show (d : ℤ) * t ≤ y by
      rw [← hem]
      exact_mod_cast (by simpa [mul_assoc] using hprod))

private theorem vaughanTypeIIRectRightCoeff_eq_zero_of_lt
    (N v l : ℕ) (t : ℤ) (ht : 1 ≤ t) (hlt : t < (2 ^ l : ℕ)) :
    vaughanTypeIIRectRightCoeff N v l t = 0 := by
  unfold vaughanTypeIIRectRightCoeff
  apply Finset.sum_eq_zero
  intro e he
  rw [if_neg]
  intro het
  have hepow : 2 ^ l ≤ e := (vaughanCanonicalDyadicBlock_pow_bounds he).1
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have htpos : 0 < t.toNat := by
    rw [← Int.natCast_pos, Int.toNat_of_nonneg ht0]
    omega
  have hetle : e ≤ t.toNat := Nat.le_of_dvd htpos het
  have htcast := Int.toNat_of_nonneg ht0
  exact (not_lt_of_ge (show (2 ^ l : ℤ) ≤ t by
    rw [← htcast]
    exact_mod_cast hepow.trans hetle)) hlt

private theorem sum_Icc_natCast_eq_int
    (A B : ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ Finset.Icc A B, f n) =
      ∑ z ∈ Finset.Icc (A : ℤ) (B : ℤ), f z := by
  refine Finset.sum_nbij' (fun n : ℕ => (n : ℤ)) Int.toNat ?_ ?_ ?_ ?_
    (fun _ _ => rfl)
  · intro n hn
    simpa only [Finset.mem_Icc, Nat.cast_le] using hn
  · intro z hz
    obtain ⟨hA, hB⟩ := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro n hn
    exact Int.toNat_natCast n
  · intro z hz
    exact Int.toNat_of_nonneg
      ((Nat.cast_nonneg A).trans (Finset.mem_Icc.mp hz).1)

/-- An active canonical Type-II shell is literally a sharp rectangular
hyperbolic character sum.  The rectangular coefficients retain the canonical
block indicators; no scalar estimate is asserted. -/
theorem vaughanTypeIICanonicalBilinearBlock_eq_rectangularSharp
    (y N u v k l q : ℕ) (χ : PrimitiveCharacter q)
    (hyN : y ≤ N)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanTypeIICanonicalBilinearBlock (fun _ => 1) y N u v k l q χ =
      rectangularSharpHyperbolicCharacterSum
        (vaughanTypeIIRectLeftCoeff N u k)
        (vaughanTypeIIRectRightCoeff N v l) y
        ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
        (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) q χ := by
  have hDS : ∀ d ∈ vaughanCanonicalDyadicBlock N u k, 0 < d :=
    fun d hd => (mem_vaughanCanonicalDyadicBlock.mp hd).1
  have hES : ∀ e ∈ vaughanCanonicalDyadicBlock N v l, 0 < e :=
    fun e he => (mem_vaughanCanonicalDyadicBlock.mp he).1
  have hactive' : 2 ^ k * 2 ^ l ≤ N := by
    simpa using (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).2
  have hlDiv : 2 ^ l ≤ N / 2 ^ k :=
    (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).2 (by
      simpa [mul_comm] using hactive')
  let F : ℕ → ℤ → ℂ := fun d t =>
    (vaughanMoebiusCoeff d * χ.1 (d : ZMod q)) *
      ((if (d : ℤ) * t ≤ y then vaughanTypeIIRectRightCoeff N v l t else 0) *
        χ.1 (t : ZMod q))
  change vaughanBilinearBlockOn vaughanMoebiusCoeff vaughanMangoldtCoeff
    (fun _ => 1) y (vaughanCanonicalDyadicBlock N u k)
      (vaughanCanonicalDyadicBlock N v l) q χ = _
  rw [vaughanBilinearBlockOn_eq_tensor _ _ _ _ _ _ _ _ hDS hES]
  have hleft :
      (∑ d ∈ vaughanCanonicalDyadicBlock N u k,
        (vaughanMoebiusCoeff d * χ.1 (d : ZMod q)) *
          ∑ t ∈ Finset.Icc (1 : ℤ) y,
            vaughanBilinearTensorCoeff vaughanMangoldtCoeff (fun _ => 1) y d
              (vaughanCanonicalDyadicBlock N v l) t * χ.1 (t : ZMod q)) =
      ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
        ∑ t ∈ Finset.Icc (1 : ℤ) N, F d t := by
    apply Finset.sum_congr rfl
    intro d hdmem
    rw [Finset.mul_sum]
    have hsub : Finset.Icc (1 : ℤ) y ⊆ Finset.Icc (1 : ℤ) N :=
      Finset.Icc_subset_Icc_right (by exact_mod_cast hyN)
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro t htmem
      rw [vaughanBilinearTensorCoeff_one_eq_ite_rectRightCoeff
        N v l y d t (hDS d hdmem) (Finset.mem_Icc.mp htmem).1]
    · intro t htN hty
      have htgt : (y : ℤ) < t := by
        simp only [Finset.mem_Icc] at hty
        have := (Finset.mem_Icc.mp htN).1
        omega
      have hnot : ¬ (d : ℤ) * t ≤ y := by
        have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hDS d hdmem
        nlinarith
      simp [F, hnot]
  rw [hleft]
  have hkEnd : (2 ^ k : ℤ) - 1 + (2 ^ k : ℕ) =
      ((2 ^ (k + 1) - 1 : ℕ) : ℤ) := by
    have hone : 1 ≤ 2 ^ (k + 1) := by
      have hpos : 0 < (2 : ℕ) ^ (k + 1) := pow_pos (by norm_num) _
      omega
    rw [Nat.cast_sub hone]
    push_cast
    rw [pow_succ]
    ring
  have hlEnd : (2 ^ l : ℤ) - 1 + (N / 2 ^ k - 2 ^ l + 1 : ℕ) =
      (N / 2 ^ k : ℕ) := by
    rw [Nat.cast_add, Nat.cast_sub hlDiv]
    push_cast
    ring
  unfold rectangularSharpHyperbolicCharacterSum
  rw [show (2 ^ k : ℤ) - 1 + 1 = ((2 ^ k : ℕ) : ℤ) by norm_num,
    hkEnd, show (2 ^ l : ℤ) - 1 + 1 = ((2 ^ l : ℕ) : ℤ) by norm_num, hlEnd]
  rw [← sum_Icc_natCast_eq_int (2 ^ k) (2 ^ (k + 1) - 1)]
  have hdSubset : vaughanCanonicalDyadicBlock N u k ⊆
      Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1) := by
    intro d hdmem
    have hb := vaughanCanonicalDyadicBlock_pow_bounds hdmem
    exact Finset.mem_Icc.mpr ⟨hb.1, by omega⟩
  rw [← Finset.sum_subset hdSubset]
  · apply Finset.sum_congr rfl
    intro d hdmem
    have hdpos := hDS d hdmem
    simp only [vaughanTypeIIRectLeftCoeff, Int.toNat_natCast, if_pos hdmem]
    refine Eq.trans (sum_Icc_natCast_eq_int 1 N (F d)).symm ?_
    refine Eq.trans ?_ (sum_Icc_natCast_eq_int (2 ^ l) (N / 2 ^ k)
      (fun x => vaughanMoebiusCoeff d * vaughanTypeIIRectRightCoeff N v l x *
        χ.1 (((d : ℤ) * x : ℤ) : ZMod q) *
          if (d : ℤ) * x ≤ y then 1 else 0))
    have htSubset : Finset.Icc (2 ^ l : ℕ) (N / 2 ^ k) ⊆
        Finset.Icc (1 : ℕ) N := by
      intro t htmem
      have htI := Finset.mem_Icc.mp htmem
      have hlpos : 0 < (2 : ℕ) ^ l := pow_pos (by norm_num) _
      exact Finset.mem_Icc.mpr ⟨hlpos.trans_le htI.1,
        htI.2.trans (Nat.div_le_self _ _)⟩
    rw [← Finset.sum_subset htSubset]
    · apply Finset.sum_congr rfl
      intro t htmem
      dsimp [F]
      by_cases hdt : (d : ℤ) * (t : ℤ) ≤ y
      · simp [hdt]
        ring
      · simp [hdt]
    · intro t htN htRect
      have htN' := Finset.mem_Icc.mp htN
      simp only [Finset.mem_Icc] at htRect
      by_cases hlow : (t : ℕ) < 2 ^ l
      · dsimp [F]
        rw [vaughanTypeIIRectRightCoeff_eq_zero_of_lt N v l t]
        · simp []
        · exact_mod_cast htN'.1
        · exact_mod_cast hlow
      · have hhigh : N / 2 ^ k < t := by omega
        have hdk : 2 ^ k ≤ d := (vaughanCanonicalDyadicBlock_pow_bounds hdmem).1
        have hnot : ¬ (d : ℤ) * (t : ℤ) ≤ y := by
          have hmul : N < d * t := by
            have hbase : N < t * 2 ^ k :=
              (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ k)).mp hhigh
            have hbase' : N < 2 ^ k * t := by simpa [mul_comm] using hbase
            exact hbase'.trans_le (Nat.mul_le_mul_right t hdk)
          exact_mod_cast (not_le_of_gt (hyN.trans_lt hmul))
        simp [F, hnot]
  · intro d hdFull hdNot
    simp [vaughanTypeIIRectLeftCoeff, hdNot]


end
end AnalyticNumberTheory.LargeSieve
