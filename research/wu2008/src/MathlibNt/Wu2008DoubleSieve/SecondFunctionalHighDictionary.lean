import SecondFunctionalUnitKernelOscillation
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalContinuousSlab

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnit
open Set MeasureTheory SecondFunctionalUnitKernel SecondFunctionalUnitPrimeFibre

/-- Independent literal closed domains from the author text, lines 2389--2394. -/
def D20 (a2 a3 b : ℝ) (x : Fin 5 → ℝ) : Prop :=
  a2 ≤ x 0 ∧ x 0 ≤ a3 ∧ a3 ≤ x 1 ∧ x 1 ≤ x 2 ∧ x 2 ≤ x 3 ∧ x 3 ≤ x 4 ∧ x 4 ≤ b

def D21 (a3 b : ℝ) (x : Fin 6 → ℝ) : Prop :=
  a3 ≤ x 0 ∧ x 0 ≤ x 1 ∧ x 1 ≤ x 2 ∧ x 2 ≤ x 3 ∧ x 3 ≤ x 4 ∧ x 4 ≤ x 5 ∧ x 5 ≤ b

/-- Strict prefix envelopes; the strict final prefix cap is retained. -/
def Q20 (a2 a3 b : ℝ) (t : Fin 4 → ℝ) : Prop :=
  a2 ≤ t 0 ∧ t 0 < a3 ∧ a3 ≤ t 1 ∧ t 1 < t 2 ∧ t 2 < t 3 ∧ t 3 < b

def Q21 (a3 b : ℝ) (t : Fin 5 → ℝ) : Prop :=
  a3 ≤ t 0 ∧ t 0 < t 1 ∧ t 1 < t 2 ∧ t 2 < t 3 ∧ t 3 < t 4 ∧ t 4 < b

/-- Constant matrices: only the six literal inequalities are expanded. -/
def C20 : Fin 6 → Fin 4 → ℝ :=
  ![![-1,0,0,0], ![1,0,0,0], ![0,-1,0,0], ![0,1,-1,0], ![0,0,1,-1], ![0,0,0,1]]
def C21 : Fin 6 → Fin 5 → ℝ :=
  ![![-1,0,0,0,0], ![1,-1,0,0,0], ![0,1,-1,0,0], ![0,0,1,-1,0],
    ![0,0,0,1,-1], ![0,0,0,0,1]]
def gamma20 (a2 a3 b : ℝ) : Fin 6 → ℝ := ![-a2,a3,-a3,0,0,b]
def gamma21 (a3 b : ℝ) : Fin 6 → ℝ := ![-a3,0,0,0,0,b]
def flags20 : Fin 6 → Bool := ![false,true,false,true,true,true]
def flags21 : Fin 6 → Bool := ![false,true,true,true,true,true]

theorem dictionary20 (a2 a3 b : ℝ) (t : Fin 4 → ℝ) :
    mask C20 (gamma20 a2 a3 b) flags20 t ↔ Q20 a2 a3 b t := by
  simp [mask, row, dot, C20, gamma20, flags20, Q20, Fin.forall_fin_succ,
    Fin.sum_univ_succ, ← sub_eq_add_neg]

theorem dictionary21 (a3 b : ℝ) (t : Fin 5 → ℝ) :
    mask C21 (gamma21 a3 b) flags21 t ↔ Q21 a3 b t := by
  simp [mask, row, dot, C21, gamma21, flags21, Q21, Fin.forall_fin_succ,
    Fin.sum_univ_succ, ← sub_eq_add_neg]

/-- Explicit coordinate witnesses, independent of all window parameters. -/
def witness20 : Fin 6 → Fin 4 := ![0,0,1,1,2,3]
def witness21 : Fin 6 → Fin 5 := ![0,0,1,2,3,4]

theorem witness20_spec : ∀ q, 1 ≤ |C20 q (witness20 q)| := by
  norm_num [Fin.forall_fin_succ, C20, witness20]
  change 1 ≤ |(1 : ℝ)| ∧ 1 ≤ |(1 : ℝ)|
  norm_num
theorem witness21_spec : ∀ q, 1 ≤ |C21 q (witness21 q)| := by
  norm_num [Fin.forall_fin_succ, C21, witness21]
  change 1 ≤ |(1 : ℝ)| ∧ 1 ≤ |(1 : ℝ)| ∧ 1 ≤ |(1 : ℝ)|
  norm_num
theorem normalized20 : ∀ q, ∃ j, 1 ≤ |C20 q j| := fun q => ⟨witness20 q, witness20_spec q⟩
theorem normalized21 : ∀ q, ∃ j, 1 ≤ |C21 q j| := fun q => ⟨witness21 q, witness21_spec q⟩

theorem Q20_empty_left (a b : ℝ) (t : Fin 4 → ℝ) : ¬ Q20 a a b t := by
  rintro ⟨h1,h2,_⟩; exact (not_lt_of_ge h1) h2

theorem Q20_empty_right (a b : ℝ) (t : Fin 4 → ℝ) : ¬ Q20 a b b t := by
  rintro ⟨_,_,h1,h2,h3,h4⟩; linarith

theorem Q21_empty (a : ℝ) (t : Fin 5 → ℝ) : ¬ Q21 a a t := by
  rintro ⟨h1,h2,h3,h4,h5,h6⟩; linarith

/-- Full labelled prime-prefix filters, defined from literal prime inequalities. -/
noncomputable def primePrefix20 (R a2 a3 b : ℝ) : Finset (Fin 4 → primeSlabPrimes R) :=
  Finset.univ.filter fun f =>
    R ^ a2 ≤ ((f 0).val : ℝ) ∧ ((f 0).val : ℝ) < R ^ a3 ∧
    R ^ a3 ≤ ((f 1).val : ℝ) ∧ (f 1).val < (f 2).val ∧
    (f 2).val < (f 3).val ∧ ((f 3).val : ℝ) < R ^ b
noncomputable def primePrefix21 (R a3 b : ℝ) : Finset (Fin 5 → primeSlabPrimes R) :=
  Finset.univ.filter fun f =>
    R ^ a3 ≤ ((f 0).val : ℝ) ∧ (f 0).val < (f 1).val ∧
    (f 1).val < (f 2).val ∧ (f 2).val < (f 3).val ∧
    (f 3).val < (f 4).val ∧ ((f 4).val : ℝ) < R ^ b

theorem power_le_coordinate {n : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin n → primeSlabPrimes R) (j : Fin n) (a : ℝ) :
    R ^ a ≤ ((f j).val : ℝ) ↔ a ≤ coordinate f j := by
  rw [← coordinate_power hR f j, Real.rpow_le_rpow_left_iff hR]
theorem coordinate_lt_power {n : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin n → primeSlabPrimes R) (j : Fin n) (a : ℝ) :
    ((f j).val : ℝ) < R ^ a ↔ coordinate f j < a := by
  rw [← coordinate_power hR f j, Real.rpow_lt_rpow_left_iff hR]
theorem prime_lt_coordinate {n : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin n → primeSlabPrimes R) (i j : Fin n) :
    (f i).val < (f j).val ↔ coordinate f i < coordinate f j := by
  have h : ((f i).val : ℝ) < ((f j).val : ℝ) ↔ coordinate f i < coordinate f j := by
    rw [← coordinate_power hR f i, ← coordinate_power hR f j, Real.rpow_lt_rpow_left_iff hR]
  exact (Nat.cast_lt (α := ℝ)).symm.trans h

theorem mem_primePrefix20 {R : ℝ} (hR : 1 < R) (a2 a3 b : ℝ)
    (f : Fin 4 → primeSlabPrimes R) :
    f ∈ primePrefix20 R a2 a3 b ↔ Q20 a2 a3 b (coordinate f) := by
  simp only [primePrefix20, Finset.mem_filter, Finset.mem_univ, true_and, Q20,
    power_le_coordinate hR, coordinate_lt_power hR, prime_lt_coordinate hR]
theorem mem_primePrefix21 {R : ℝ} (hR : 1 < R) (a3 b : ℝ)
    (f : Fin 5 → primeSlabPrimes R) :
    f ∈ primePrefix21 R a3 b ↔ Q21 a3 b (coordinate f) := by
  simp only [primePrefix21, Finset.mem_filter, Finset.mem_univ, true_and, Q21,
    power_le_coordinate hR, coordinate_lt_power hR, prime_lt_coordinate hR]

theorem primePrefix20_exact {R : ℝ} (hR : 1 < R) (a2 a3 b : ℝ) :
    primePrefix20 R a2 a3 b = Finset.univ.filter
      (fun f => mask C20 (gamma20 a2 a3 b) flags20 (coordinate f)) := by
  ext f; simp [mem_primePrefix20 hR, dictionary20]
theorem primePrefix21_exact {R : ℝ} (hR : 1 < R) (a3 b : ℝ) :
    primePrefix21 R a3 b = Finset.univ.filter
      (fun f => mask C21 (gamma21 a3 b) flags21 (coordinate f)) := by
  ext f; simp [mem_primePrefix21 hR, dictionary21]

theorem primePrefix20_empty_left {R : ℝ} (hR : 1 < R) (a b : ℝ) :
    primePrefix20 R a a b = ∅ := by
  ext f; simp [mem_primePrefix20 hR, Q20_empty_left]
theorem primePrefix20_empty_right {R : ℝ} (hR : 1 < R) (a b : ℝ) :
    primePrefix20 R a b b = ∅ := by
  ext f; simp [mem_primePrefix20 hR, Q20_empty_right]
theorem primePrefix21_empty {R : ℝ} (hR : 1 < R) (a : ℝ) :
    primePrefix21 R a a = ∅ := by
  ext f; simp [mem_primePrefix21 hR, Q21_empty]

end Wu2008DoubleSieve.HighUnit
