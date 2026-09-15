import Wu08SmallBoundaryTerminal

noncomputable section
open Finset Real Set LiLiuPrereqBuchstab
open scoped Classical
open Wu2008DoubleSieve
namespace Wu08FirstPrimeFour.SmallBoundaryRecovery
open FourRoughClosedMass SmallGrid SmallBoundary

def firstBand (N : ℕ) (a b : ℝ) : Finset SmallGrid.Quad :=
  (FourRoughClosedMass.box N).filter fun q => a ≤ coord N q.1 ∧ coord N q.1 ≤ b

def orderBand (N : ℕ) (s : ℝ) : Finset SmallGrid.Quad :=
  (FourRoughClosedMass.box N).filter fun q =>
    coord N q.2.1 ≤ coord N q.1 ∧ coord N q.1 ≤ coord N q.2.1+s

theorem coord_mem_closed {N p : ℕ} {a b : ℝ} (hN : 1 < N) (hp : p.Prime)
    (ha : a ≤ coord N p) (hb : coord N p ≤ b) :
    p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b) := by
  apply (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) b)).mpr
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  refine ⟨hp,?_,?_⟩
  · exact (rpow_le_rpow_of_exponent_le hn ha).trans_eq (rpow_coord hN hp.pos)
  · exact (rpow_coord hN hp.pos).symm.trans_le (rpow_le_rpow_of_exponent_le hn hb)

theorem firstBand_paid {N : ℕ} {a b ε : ℝ} (hN : 1 < N)
    (hm : windowMass N ≤ 5) (hε : 0 ≤ ε) (hab : a ≤ b)
    (hp : (∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b), 1/(p : ℝ)) ≤ 15*(b-a)+ε) :
    reciprocalMass (firstBand N a b) ≤ 125*(15*(b-a)+ε) := by
  apply (sum_le_sum_of_subset_of_nonneg (s := firstBand N a b)
    (t := primesIcc ((N : ℝ)^a) ((N : ℝ)^b) ×ˢ window N ×ˢ window N ×ˢ window N)
    ?_ (by intros; positivity)).trans (first_strip_reciprocal hm hε hab hp)
  intro q hq
  obtain ⟨hq,ha,hb⟩ := mem_filter.mp hq
  obtain ⟨hx,ht⟩ := mem_product.mp hq
  have hprime := ((mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) (1/3 : ℝ))).mp hx).1
  exact mem_product.mpr ⟨coord_mem_closed hN hprime ha hb,ht⟩

theorem row_paid {N b : ℕ} {s ε : ℝ} (hN : 1 < N) (hs : 0 ≤ s)
    (hb : b ∈ window N)
    (hstrip : ∀ a c : ℝ, a ∈ low → c ∈ low → a ≤ c →
      (∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^c), 1/(p : ℝ)) ≤ 15*(c-a)+ε) :
    (∑ a ∈ (window N).filter (fun a => coord N b ≤ coord N a ∧ coord N a ≤ coord N b+s),
      1/(a : ℝ)) ≤ 15*s+ε := by
  have hb' : coord N b ∈ low := closed_coord hN hb
  let c := min (coord N b+s) (1/3 : ℝ)
  have hbc : coord N b ≤ c := le_min (by linarith) hb'.2
  have hc : c ∈ low := ⟨hb'.1.trans hbc,min_le_right _ _⟩
  have hsub : (window N).filter (fun a => coord N b ≤ coord N a ∧ coord N a ≤ coord N b+s) ⊆
      primesIcc ((N : ℝ)^(coord N b)) ((N : ℝ)^c) := by
    intro a ha
    obtain ⟨ha,hba,hab⟩ := mem_filter.mp ha
    have ha' : coord N a ∈ low := closed_coord hN ha
    have hprime := ((mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) (1/3 : ℝ))).mp ha).1
    exact coord_mem_closed hN hprime hba (le_min hab ha'.2)
  have hmass := (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans
    (hstrip _ _ hb' hc hbc)
  have hcu : c ≤ coord N b+s := min_le_left _ _
  linarith only [hmass,hcu]

theorem orderBand_paid {N : ℕ} {s ε : ℝ} (hN : 1 < N)
    (hm : windowMass N ≤ 5) (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (hstrip : ∀ a b : ℝ, a ∈ low → b ∈ low → a ≤ b →
      (∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b), 1/(p : ℝ)) ≤ 15*(b-a)+ε) :
    reciprocalMass (orderBand N s) ≤ 125*(15*s+ε) := by
  have heq : reciprocalMass (orderBand N s) =
      (∑ b ∈ window N, (1/(b : ℝ))*
        ∑ a ∈ (window N).filter (fun a => coord N b ≤ coord N a ∧ coord N a ≤ coord N b+s),
          1/(a : ℝ))*windowMass N^2 := by
    simp only [reciprocalMass,orderBand,FourRoughClosedMass.box,sum_filter,sum_product,
      fourModulusProduct,Nat.cast_mul]
    simp only [div_eq_mul_inv,mul_inv_rev]
    rw [sum_comm]
    simp only [windowMass,sum_mul,mul_sum,pow_two]
    conv_rhs =>
      arg 2
      ext c
      rw [sum_comm]
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro b _
    rw [sum_comm]
    apply sum_congr rfl
    intro c _
    rw [sum_comm]
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro a _
    split_ifs <;> ring
  rw [heq]
  have hm0 : 0 ≤ windowMass N := sum_nonneg (by intros; positivity)
  have hE : 0 ≤ 15*s+ε := by positivity
  have hrow : (∑ b ∈ window N, (1/(b : ℝ))*
      ∑ a ∈ (window N).filter (fun a => coord N b ≤ coord N a ∧ coord N a ≤ coord N b+s),
        1/(a : ℝ)) ≤ windowMass N*(15*s+ε) := by
    rw [windowMass,sum_mul]
    exact sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (row_paid hN hs hb hstrip) (by positivity)
  have hp : windowMass N^3 ≤ 125 := (pow_le_pow_left₀ hm0 hm 3).trans_eq (by norm_num)
  calc
    _ ≤ (windowMass N*(15*s+ε))*windowMass N^2 := mul_le_mul_of_nonneg_right hrow (sq_nonneg _)
    _ = windowMass N^3*(15*s+ε) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hp hE

#check firstBand
#print axioms firstBand
#check orderBand
#print axioms orderBand
#check coord_mem_closed
#print axioms coord_mem_closed
#check firstBand_paid
#print axioms firstBand_paid
#check row_paid
#print axioms row_paid
#check orderBand_paid
#print axioms orderBand_paid
end Wu08FirstPrimeFour.SmallBoundaryRecovery
