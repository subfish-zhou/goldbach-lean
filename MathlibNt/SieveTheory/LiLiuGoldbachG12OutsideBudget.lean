import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFSmall
import MathlibNt.SieveTheory.LiLiuFouvryG9ExternalExceptional

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF

namespace G12OutsideBudget

/-- The actual normalized output fibre, restricted to any submother. -/
def fibre (N : ℕ) (A : Finset GoldbachG12LinkedAtom) (n : ℕ) : ℝ :=
  ∑ x ∈ A.filter (fun x => goldbachG12LinkedOutput N x = n),
    goldbachG12NormalizedCoefficient N x.1

theorem fibre_le_twenty {N : ℕ} (hN : 2 ≤ N) (ε : ℝ)
    (A : Finset GoldbachG12LinkedAtom) (hA : A ⊆ goldbachG12LinkedAtoms N ε) (n : ℕ) :
    fibre N A n ≤ 20 := by
  calc
    _ ≤ goldbachG12LinkedOutputWeight N ε n :=
      sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hA)
        (fun x _ _ => (goldbachG12NormalizedCoefficient_bounds N x.1).1)
    _ ≤ 20 := goldbachG12LinkedOutputWeight_le_twenty hN ε n

/-- All genuine outputs are positive and at most N. -/
theorem output_mem {N : ℕ} {ε : ℝ} {x : GoldbachG12LinkedAtom}
    (hx : x ∈ goldbachG12LinkedAtoms N ε) :
    goldbachG12LinkedOutput N x ∈ Icc 1 N := by
  obtain ⟨hm,hr⟩ := mem_sigma.mp hx
  exact mem_Icc.mpr ⟨goldbachG12LinkedPrimeWindow_output_pos hm hr,
    Nat.sub_le _ _⟩

/-- Finite tests are paid after output pushforward, never tuplewise. -/
theorem test_le {N : ℕ} (hN : 2 ≤ N) (ε : ℝ)
    (A : Finset GoldbachG12LinkedAtom) (hA : A ⊆ goldbachG12LinkedAtoms N ε)
    (B : Finset ℕ) :
    (∑ x ∈ A.filter (fun x => goldbachG12LinkedOutput N x ∈ B),
      goldbachG12NormalizedCoefficient N x.1) ≤ 20 * (B.card : ℝ) := by
  rw [← sum_fiberwise_eq_sum_filter A B (goldbachG12LinkedOutput N)]
  calc
    _ ≤ ∑ _n ∈ B, (20 : ℝ) := sum_le_sum fun n _ => fibre_le_twenty hN ε A hA n
    _ = _ := by simp [mul_comm]

def mass (N : ℕ) (A : Finset GoldbachG12LinkedAtom) : ℝ :=
  ∑ x ∈ A, goldbachG12NormalizedCoefficient N x.1

def divisibility (N : ℕ) (A : Finset GoldbachG12LinkedAtom) (d : ℕ) : ℝ :=
  ∑ x ∈ A, if d ∣ goldbachG12LinkedOutput N x
    then goldbachG12NormalizedCoefficient N x.1 else 0

def residue (N : ℕ) (A : Finset GoldbachG12LinkedAtom) (d : ℕ) : ℝ :=
  divisibility N A d - mass N A / (d.totient : ℝ)

theorem mass_le {N : ℕ} (hN : 2 ≤ N) (ε : ℝ)
    (A : Finset GoldbachG12LinkedAtom) (hA : A ⊆ goldbachG12LinkedAtoms N ε) :
    mass N A ≤ 20 * N := by
  have he : A.filter (fun x => goldbachG12LinkedOutput N x ∈ Icc 1 N) = A :=
    filter_eq_self.mpr fun x hx => output_mem (hA hx)
  have hb := test_le hN ε A hA (Icc 1 N)
  rw [he] at hb
  simpa [mass, Nat.card_Icc] using hb

theorem multiples_card_le (N d : ℕ) :
    ((Icc 1 N).filter (fun n => d ∣ n)).card ≤ N / d := by
  rw [← Nat.card_multiples N d]
  apply card_le_card_of_injOn (fun n => n-1)
  · intro n hn
    obtain ⟨hn,hd⟩ := mem_filter.mp hn
    obtain ⟨hn1,hnN⟩ := mem_Icc.mp hn
    apply mem_filter.mpr
    constructor
    · exact mem_range.mpr (by dsimp; omega)
    · simpa [Nat.sub_add_cancel hn1] using hd
  · intro n hn m hm he
    have hn1 := (mem_Icc.mp (mem_filter.mp hn).1).1
    have hm1 := (mem_Icc.mp (mem_filter.mp hm).1).1
    dsimp at he
    omega

theorem divisibility_le {N : ℕ} (hN : 2 ≤ N) (ε : ℝ)
    (A : Finset GoldbachG12LinkedAtom) (hA : A ⊆ goldbachG12LinkedAtoms N ε) (d : ℕ) :
    divisibility N A d ≤ 20 * (N / d : ℕ) := by
  have he : A.filter (fun x => goldbachG12LinkedOutput N x ∈
      (Icc 1 N).filter (fun n => d ∣ n)) =
      A.filter (fun x => d ∣ goldbachG12LinkedOutput N x) := by
    ext x
    simp only [mem_filter]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,
      fun h => ⟨h.1,output_mem (hA h.1),h.2⟩⟩
  have hb := test_le hN ε A hA ((Icc 1 N).filter (fun n => d ∣ n))
  rw [he, sum_filter] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (multiples_card_le N d))
    (by norm_num))

/-- An unconditional majorant for the real normalized G12 residue. -/
theorem residue_majorant {N : ℕ} (hN : 2 ≤ N) (ε : ℝ)
    (A : Finset GoldbachG12LinkedAtom) (hA : A ⊆ goldbachG12LinkedAtoms N ε)
    {d : ℕ} (hd : 1 ≤ d) : |residue N A d| ≤ (20 * N) / d.totient := by
  have hφ : (0 : ℝ) < d.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d)
  have hm0 : 0 ≤ mass N A := sum_nonneg fun x _ =>
    (goldbachG12NormalizedCoefficient_bounds N x.1).1
  have hv0 : 0 ≤ divisibility N A d := sum_nonneg fun x _ => by
    split_ifs
    · exact (goldbachG12NormalizedCoefficient_bounds N x.1).1
    · exact le_rfl
  have hm := div_le_div_of_nonneg_right (mass_le hN ε A hA) hφ.le
  have hv : divisibility N A d ≤ (20 * N) / d.totient := by
    calc
      _ ≤ (20 : ℝ) * (N / d : ℕ) := divisibility_le hN ε A hA d
      _ ≤ 20 * ((N : ℝ) / d) := mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)
      _ = (20 * N) / d := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hφ
        (by exact_mod_cast Nat.totient_le d)
  rw [residue, abs_le]
  constructor
  · linarith
  · have := div_nonneg hm0 hφ.le
    linarith

end G12OutsideBudget
