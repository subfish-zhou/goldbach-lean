import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughConnection
import MathlibNt.SieveTheory.LiLiuGoldbachG11SwitchedTransport

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open Classical in
/-- The original three-low/one-high labels are exactly a restriction of the
parameterized G11 labels, not an enlargement of the count. -/
theorem goldbachG12Labels_eq_filter (N : ℕ) (z b c : ℝ) :
    goldbachG12Labels N z b c =
      (goldbachG11Labels N z c).filter
        (fun v => (v.2.1 : ℝ) ≤ b ∧ b ≤ (v.1 : ℝ)) := by
  ext v
  rcases v with ⟨t, s, r, q⟩
  rw [Finset.mem_filter]
  constructor
  · intro hv
    refine ⟨goldbachG12Labels_subset_goldbachG11Labels N z b c hv, ?_⟩
    obtain ⟨_, _, _, _, _, _, _, _, hsb, hbt, _⟩ :=
      mem_goldbachG12Labels_iff.mp hv
    exact ⟨hsb, hbt⟩
  · rintro ⟨hv, hsb, hbt⟩
    obtain ⟨hr, hq, hs, ht, hcop, hzr, hrq, hqs, _, htc⟩ :=
      mem_goldbachG11Labels_iff.mp hv
    exact mem_goldbachG12Labels_iff.mpr
      ⟨hr, hq, hs, ht, hcop, hzr, hrq, hqs, hsb, hbt, htc⟩

/-- The cross restriction does not depend on the rough cofactor k. -/
theorem goldbachG12_switch_predicate (v : GoldbachG11Label) (k : ℕ) (b : ℝ) :
    ((goldbachG11SwitchedBodyOf v k).2.1 : ℝ) ≤ b ∧
        b ≤ ((goldbachG11SwitchedBodyOf v k).1 : ℝ) ↔
      (v.2.1 : ℝ) ≤ b ∧ b ≤ (v.1 : ℝ) := Iff.rfl

/-- Same switched body type, with both cross endpoints retained. -/
noncomputable def goldbachG12CrossSwitchedBodies (N : ℕ) (z b c : ℝ) :
    Finset GoldbachG11SwitchedBody := by
  classical
  exact (goldbachG11SwitchedBodies N z c).filter
    (fun u => (u.2.1 : ℝ) ≤ b ∧ b ≤ (u.1 : ℝ))

theorem mem_goldbachG12CrossSwitchedBodies_iff {N t s q k : ℕ} {z b c : ℝ} :
    (⟨t, s, q, k⟩ : GoldbachG11SwitchedBody) ∈
        goldbachG12CrossSwitchedBodies N z b c ↔
      q.Prime ∧ s.Prime ∧ t.Prime ∧ Nat.Coprime (q * s * t) N ∧
        z ≤ (q : ℝ) ∧ q ≤ s ∧ (s : ℝ) ≤ b ∧ b ≤ (t : ℝ) ∧
          (t : ℝ) ≤ c ∧ 1 ≤ k ∧ k ≤ N ∧
            SurvivesSieve 1 q k ∧ q * s * t * k < N := by
  classical
  rw [goldbachG12CrossSwitchedBodies, Finset.mem_filter,
    mem_goldbachG11SwitchedBodies_iff]
  constructor
  · rintro ⟨⟨hq, hs, ht, hcop, hzq, hqs, _, htc, hk1, hkN, hrough, hprod⟩,
      hsb, hbt⟩
    exact ⟨hq, hs, ht, hcop, hzq, hqs, hsb, hbt, htc, hk1, hkN, hrough, hprod⟩
  · rintro ⟨hq, hs, ht, hcop, hzq, hqs, hsb, hbt, htc, hk1, hkN, hrough, hprod⟩
    exact ⟨⟨hq, hs, ht, hcop, hzq, hqs, by exact_mod_cast hsb.trans hbt,
      htc, hk1, hkN, hrough, hprod⟩, hsb, hbt⟩

open Classical in
/-- Exact finite switch of the original cross rough sum. No restrictions on
N, epsilon, or endpoint order are needed; the output-prime fibre is unchanged. -/
theorem goldbachG12RoughSum_eq_crossSwitched (N : ℕ) (ε z b c : ℝ) :
    (∑ v ∈ goldbachG12Labels N z b c, goldbachG11RoughCount N ε v) =
      ∑ u ∈ (goldbachG11SwitchedBodies N z c).filter
          (fun u => (u.2.1 : ℝ) ≤ b ∧ b ≤ (u.1 : ℝ)),
        ((goldbachG11FirstPrimeFiber N ε z u).card : ℤ) := by
  have hswitch := goldbachG11Switch_filter_count N ε z c
    (fun u => (u.2.1 : ℝ) ≤ b ∧ b ≤ (u.1 : ℝ))
  rw [goldbachG12Labels_eq_filter]
  simp only [Finset.sum_filter] at hswitch ⊢
  convert hswitch using 1
  · apply Finset.sum_congr rfl
    intro v _
    by_cases h : (v.2.1 : ℝ) ≤ b ∧ b ≤ (v.1 : ℝ)
    · simp [goldbachG11SwitchedBodyOf, goldbachG11RoughCount, h]
    · simp [goldbachG11SwitchedBodyOf, h]
  · apply Finset.sum_congr rfl
    intro u _
    by_cases h : (u.2.1 : ℝ) ≤ b ∧ b ≤ (u.1 : ℝ) <;> simp [h]

theorem goldbachG12RoughSum_eq_crossSwitchedBodies (N : ℕ) (ε z b c : ℝ) :
    (∑ v ∈ goldbachG12Labels N z b c, goldbachG11RoughCount N ε v) =
      ∑ u ∈ goldbachG12CrossSwitchedBodies N z b c,
        ((goldbachG11FirstPrimeFiber N ε z u).card : ℤ) :=
  goldbachG12RoughSum_eq_crossSwitched N ε z b c

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
