import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanConvolutionAPCount
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanWangDingSource

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiuWeight

/-- Identification with the counting component of the actual production sum.
The main function, its argument N/a in real arithmetic, and its normalization
are left literally unchanged. -/
theorem liuMainPanCoprimeIntervalSum_eq_count_sub_main
    (main : ℝ → ℝ) (N z y A₁ A₂ q l : ℕ) :
    liuMainPanCoprimeIntervalSum main N A₁ A₂ q l (liuWeight N z y) =
      liuCoprimeIntervalCount N z y A₁ A₂ q l -
        ∑ a ∈ Ioc A₁ A₂, if a.Coprime q then
          liuWeight N z y a * (main ((N : ℝ) / a) / Nat.totient q) else 0 := by
  unfold liuMainPanCoprimeIntervalSum liuCoprimeIntervalCount liuScaledAPError
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

/-- Explicit domination by the untruncated beta sum, after whole-a regrouping. -/
theorem liuCoprimeIntervalCount_le_sum_beta (N z y A₁ A₂ q l : ℕ) :
    liuCoprimeIntervalCount N z y A₁ A₂ q l ≤
      ∑ n ∈ liuAPCarrier N q l, liuBeta N z y n := by
  rw [liuCoprimeIntervalCount_eq_sum_betaInterval]
  exact Finset.sum_le_sum fun n _ => liuBetaInterval_le_beta N z y A₁ A₂ q n

/-- Source-specialized counting estimate, uniform in arbitrary interval cuts,
including reversed/empty intervals. No reduced-residue hypothesis is used. -/
theorem liuSourceCoprimeIntervalCount_le
    (N A₁ A₂ q l : ℕ) (hq : 0 < q) :
    (∑ a ∈ Ioc A₁ A₂, if a.Coprime q then
      liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
        (AnalyticNumberTheory.Sieve.primesInAPBelow N a q l : ℝ) else 0) ≤
      3 * ((N : ℝ) / q + 1) :=
  liuCoprimeIntervalCount_le_three_mul_real_div_add_one
    N (liuSourceZ10 N) (liuSourceY3 N) A₁ A₂ q l hq

/-- The exact interval in the Pan--Ding--Wang consumer. -/
theorem liuPanSourceCoprimeIntervalCount_le
    (N q l : ℕ) (B : ℝ) (hq : 0 < q) :
    (∑ a ∈ Ioc (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N),
      if a.Coprime q then liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
        (AnalyticNumberTheory.Sieve.primesInAPBelow N a q l : ℝ) else 0) ≤
      3 * ((N : ℝ) / q + 1) :=
  liuSourceCoprimeIntervalCount_le N _ _ q l hq

/-- With genuine support containment and a reduced residue, neither retained
filter removes an effective divisor. The support condition is explicit:
arbitrary truncations admit only the domination theorem above. -/
theorem liuCoprimeIntervalCount_eq_sum_beta_of_support
    (N z y A₁ A₂ q l : ℕ) (hl : l.Coprime q)
    (hsupp : ∀ a, liuWeight N z y a ≠ 0 → a ∈ Ioc A₁ A₂) :
    liuCoprimeIntervalCount N z y A₁ A₂ q l =
      ∑ n ∈ liuAPCarrier N q l, liuBeta N z y n := by
  rw [liuCoprimeIntervalCount_eq_sum_betaInterval]
  apply Finset.sum_congr rfl
  intro n hn
  have hnc : n.Coprime q := by
    change n.gcd q = 1
    rw [(Finset.mem_filter.mp hn).2.gcd_eq]
    exact hl
  unfold liuBetaInterval liuBeta
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hw : liuWeight N z y a = 0
  · simp [hw]
  · rw [if_pos ⟨hsupp a hw, hnc.of_dvd_left (Nat.dvd_of_mem_divisors ha)⟩]

/-- Exact full-beta regrouping for the source interval whenever its known
support-containment threshold holds. This is the only place reducedness is
needed; none of the upper bounds require it. -/
theorem liuPanSourceCoprimeIntervalCount_eq_sum_beta
    (N q l : ℕ) (B : ℝ) (hl : l.Coprime q)
    (hlow : liuPanSourceIntervalLower N B < liuSourceZ10 N) :
    liuCoprimeIntervalCount N (liuSourceZ10 N) (liuSourceY3 N)
      (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q l =
        ∑ n ∈ liuAPCarrier N q l,
          liuBeta N (liuSourceZ10 N) (liuSourceY3 N) n := by
  apply liuCoprimeIntervalCount_eq_sum_beta_of_support _ _ _ _ _ _ _ hl
  intro a ha
  exact liuWeight_support_mem_panSourceInterval hlow ha

end MathlibNt.SieveTheory.LiuWeight