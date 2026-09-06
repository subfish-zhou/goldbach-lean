import MathlibNt.SieveTheory.Liu.LogarithmicIntegral.LiuTrueLiPan

/-!
# Canonical Pan--Wang--Ding source theorem interface

This module records the weighted aggregate residue-class interface motivated by
Corollary (2.30) of Pan--Ding--Wang (1975), deduced there from Theorem 2
(1.2).  The corollary carries the squarefree modulus weight
`3^ν(q) |μ(q)|` and is uniform over coefficient functions with `|f(a)| ≤ 1`;
hence varying Chen sources are compatible with its quantifier order.  The
source gives the concrete choice `B = 2A + 24`; the interface below
existentially weakens that value.

The endpoint interface below uses only `y = x = N`, which is the sole prefix
consumed by Liu's `eqn-r` lane.  This avoids the previous, unsupported
strengthening to every small natural prefix.  Two source-correspondence bridges
remain separate: the zero-extended `liuWeight` must be identified with a source
interval `log^(2B) N < A₁ ≤ a ≤ A₂ < N^(1-ε)`, and the paper's unspecified
additive normalization of `li` must be related to the chosen normalization.

The analytic theorem itself remains an explicit proposition.  No primitive-
character `L¹` majorant is inferred from it: such a majorant is strictly
stronger and suffers a genuine weighted-conductor resonance obstruction.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset

/-- Natural cutoff whose `range` represents the source's strict real inequality. -/
noncomputable def panSourceStrictModulusCutoff (N : ℕ) (B : ℝ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B)

/-- Membership in the source cutoff is exactly the paper's strict real
inequality; in particular this also handles the case where the real endpoint is
an integer. -/
theorem mem_range_panSourceStrictModulusCutoff_iff (q N : ℕ) (B : ℝ) :
    q ∈ range (panSourceStrictModulusCutoff N B) ↔
      (q : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B := by
  rw [Finset.mem_range, panSourceStrictModulusCutoff, Nat.lt_ceil]

/-- Once `log N > 1`, every modulus in Lean's closed floor cutoff with exponent
`B+1` satisfies the source's strict real cutoff with exponent `B`. -/
theorem range_panModulusCutoff_add_one_subset_sourceStrict
    (N : ℕ) (B : ℝ) (hN : 0 < N) (hlog : 1 < Real.log (N : ℝ)) :
    range (panModulusCutoff N (B + 1) + 1) ⊆
      range (panSourceStrictModulusCutoff N B) := by
  intro q hq
  rw [mem_range_panSourceStrictModulusCutoff_iff]
  have hqNat : q ≤ panModulusCutoff N (B + 1) := by
    simpa [Finset.mem_range] using hq
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogpos : 0 < Real.log (N : ℝ) := lt_trans (by norm_num) hlog
  have hpowBpos : 0 < Real.log (N : ℝ) ^ B :=
    Real.rpow_pos_of_pos hlogpos B
  have hpowB1pos : 0 < Real.log (N : ℝ) ^ (B + 1) :=
    Real.rpow_pos_of_pos hlogpos (B + 1)
  have hendpoint_nonneg :
      0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1) :=
    (div_nonneg (Real.rpow_nonneg hNreal.le _) hpowB1pos.le)
  have hq_le_shifted :
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) /
        Real.log (N : ℝ) ^ (B + 1) := by
    calc
      (q : ℝ) ≤ (panModulusCutoff N (B + 1) : ℕ) := by exact_mod_cast hqNat
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) /
          Real.log (N : ℝ) ^ (B + 1) := by
        unfold panModulusCutoff
        exact Nat.floor_le hendpoint_nonneg
  have hshifted_lt_source :
      (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1) <
        (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B := by
    rw [Real.rpow_add hlogpos, Real.rpow_one]
    apply (div_lt_div_iff₀ (mul_pos hpowBpos hlogpos) hpowBpos).2
    have hnum : 0 < (N : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hNreal _
    exact mul_lt_mul_of_pos_left
      (lt_mul_of_one_lt_right hpowBpos hlog) hnum
  exact hq_le_shifted.trans_lt hshifted_lt_source

/-- For each fixed paper exponent `B`, using `B+1` in the existing Lean cutoff
is eventually source-faithful at the strict endpoint. -/
theorem eventually_range_panModulusCutoff_add_one_subset_sourceStrict (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      range (panModulusCutoff N (B + 1) + 1) ⊆
        range (panSourceStrictModulusCutoff N B) := by
  have hlogReal : ∀ᶠ x : ℝ in atTop, 1 < Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop 1)
  have hlogNat : ∀ᶠ N : ℕ in atTop, 1 < Real.log (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  filter_upwards [hlogNat, eventually_ge_atTop (1 : ℕ)] with N hlog hN
  exact range_panModulusCutoff_add_one_subset_sourceStrict N B hN hlog

/-- Threshold form of the eventual strict-endpoint bridge. -/
theorem exists_range_panModulusCutoff_add_one_subset_sourceStrict (B : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      range (panModulusCutoff N (B + 1) + 1) ⊆
        range (panSourceStrictModulusCutoff N B) :=
  eventually_atTop.mp
    (eventually_range_panModulusCutoff_add_one_subset_sourceStrict B)

/-- Integer lower endpoint used to place Liu's zero-extended source inside the
strict interval required by Pan--Ding--Wang. -/
noncomputable def liuPanSourceIntervalLower (N : ℕ) (B : ℝ) : ℕ :=
  Nat.floor (Real.log N ^ (2 * B)) + 1

/-- Integer upper endpoint at Liu's exact two-thirds support scale. -/
noncomputable def liuPanSourceIntervalUpper (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (2 / 3 : ℝ))

/-- The lower endpoint is strictly above the logarithmic source threshold. -/
theorem log_rpow_lt_liuPanSourceIntervalLower (N : ℕ) (B : ℝ) :
    Real.log N ^ (2 * B) < (liuPanSourceIntervalLower N B : ℝ) := by
  unfold liuPanSourceIntervalLower
  exact_mod_cast Nat.lt_floor_add_one (Real.log N ^ (2 * B))

/-- For `N > 1`, the two-thirds upper endpoint is strictly below the fixed
`N^(3/4)` source ceiling used in the Pan corollary. -/
theorem liuPanSourceIntervalUpper_lt_rpow_three_fourths
    {N : ℕ} (hN : 1 < N) :
    (liuPanSourceIntervalUpper N : ℝ) < (N : ℝ) ^ (3 / 4 : ℝ) := by
  have hfloor :
      (liuPanSourceIntervalUpper N : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
    unfold liuPanSourceIntervalUpper
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  exact hfloor.trans_lt (Real.rpow_lt_rpow_of_exponent_lt
    (by exact_mod_cast hN) (by norm_num : (2 / 3 : ℝ) < 3 / 4))

/-- Liu's tenth-power source cutoff lies below the two-thirds Pan endpoint. -/
theorem liuSourceZ10_le_liuPanSourceIntervalUpper
    {N : ℕ} (hN : 1 ≤ N) :
    liuSourceZ10 N ≤ liuPanSourceIntervalUpper N := by
  unfold liuSourceZ10 liuPanSourceIntervalUpper
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hN) (by norm_num : (1 / 10 : ℝ) ≤ 2 / 3)

/-- For every fixed Pan exponent, the logarithmic lower endpoint is eventually
strictly below Liu's `N^(1/10)` source cutoff. -/
theorem eventually_liuPanSourceIntervalLower_lt_liuSourceZ10 (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      liuPanSourceIntervalLower N B < liuSourceZ10 N := by
  have hsmall : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (2 * B) ≤ (1 / 2 : ℝ) * x ^ (1 / 10 : ℝ) := by
    have hbound :=
      (isLittleO_log_rpow_rpow_atTop (2 * B)
        (by norm_num : (0 : ℝ) < 1 / 10)).bound
        (show 0 < (1 / 2 : ℝ) by norm_num)
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) _)] at hx
    exact hx
  have hlarge : ∀ᶠ x : ℝ in atTop,
      (4 : ℝ) ≤ x ^ (1 / 10 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop 4)
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmall
  have hlargeNat := tendsto_natCast_atTop_atTop.eventually hlarge
  filter_upwards [hsmallNat, hlargeNat, eventually_ge_atTop (2 : ℕ)] with
      N hlog hpow hN
  have hlognonneg : 0 ≤ Real.log (N : ℝ) ^ (2 * B) :=
    Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hsum :
      Real.log (N : ℝ) ^ (2 * B) + 2 ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    linarith
  have hfloor := Nat.floor_mono hsum
  have hadd :
      Nat.floor (Real.log (N : ℝ) ^ (2 * B) + 2) =
        Nat.floor (Real.log (N : ℝ) ^ (2 * B)) + 2 := by
    simpa using Nat.floor_add_natCast hlognonneg 2
  rw [hadd] at hfloor
  unfold liuPanSourceIntervalLower liuSourceZ10
  omega

/-- All source-side interval and coefficient hypotheses needed for the Liu
specialization of Corollary `(2.30)` hold eventually (with paper ε = 1/4). -/
theorem eventually_liuPanSourceInterval_hypotheses (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log N ^ (2 * B) < (liuPanSourceIntervalLower N B : ℝ) ∧
      liuPanSourceIntervalLower N B ≤ liuPanSourceIntervalUpper N ∧
      (liuPanSourceIntervalUpper N : ℝ) < (N : ℝ) ^ (3 / 4 : ℝ) ∧
      ∀ a : ℕ,
        |liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a| ≤ 1 := by
  filter_upwards [eventually_liuPanSourceIntervalLower_lt_liuSourceZ10 B,
    eventually_ge_atTop (2 : ℕ)] with N hlow hN
  refine ⟨log_rpow_lt_liuPanSourceIntervalLower N B, ?_,
    liuPanSourceIntervalUpper_lt_rpow_three_fourths (by omega), ?_⟩
  · exact (Nat.le_of_lt hlow).trans
      (liuSourceZ10_le_liuPanSourceIntervalUpper (by omega))
  · intro a
    exact abs_liuWeight_le_one N (liuSourceZ10 N) (liuSourceY3 N) a

/-- Conditional finite support bridge.  Once the logarithmic lower endpoint is
below Liu's `N^(1/10)` cutoff, every nonzero source coefficient lies in the
Pan interval `(A₁,A₂]`. -/
theorem liuWeight_support_mem_panSourceInterval
    {N a : ℕ} {B : ℝ}
    (hlow : liuPanSourceIntervalLower N B < liuSourceZ10 N)
    (ha : liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a ≠ 0) :
    a ∈ Ioc (liuPanSourceIntervalLower N B)
      (liuPanSourceIntervalUpper N) := by
  have hsupp : LiuWeightSupport N (liuSourceZ10 N) (liuSourceY3 N) a := by
    by_contra hnot
    exact ha (liuWeight_eq_zero_iff.mpr hnot)
  rcases liuWeightSupport_iff.mp hsupp with ⟨p₁, p₂, hp, rfl⟩
  have hp₂pos : 0 < p₂ := hp.2.1.pos
  have hp₁le : p₁ ≤ p₁ * p₂ := by
    calc
      p₁ = p₁ * 1 := by simp
      _ ≤ p₁ * p₂ := Nat.mul_le_mul_left p₁ hp₂pos
  have hlower : liuPanSourceIntervalLower N B < p₁ * p₂ :=
    hlow.trans (hp.2.2.1.trans_le hp₁le)
  have hroot := liuWeightSupport_le_rpow_two_thirds hsupp
  have hupper : p₁ * p₂ ≤ liuPanSourceIntervalUpper N := by
    unfold liuPanSourceIntervalUpper
    rw [Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
    exact hroot
  exact Finset.mem_Ioc.mpr ⟨hlower, hupper⟩

/-- At a fixed endpoint, Liu's zero-extended coprime source sum is exactly the
Pan interval sum once the eventual logarithmic lower-cutoff inequality holds. -/
theorem liuMainPanCoprimeSum_eq_panSourceInterval
    (main : ℝ → ℝ) {N q l : ℕ} {B : ℝ} (hN : 1 ≤ N)
    (hlow : liuPanSourceIntervalLower N B < liuSourceZ10 N) :
    liuMainPanCoprimeSum main N N q l
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) =
      liuMainPanCoprimeIntervalSum main N
        (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q l
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
  apply liuMainPanCoprimeSum_eq_sourceIntervalSum
  · have hpow : (N : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ N by exact_mod_cast hN)
        (show (2 / 3 : ℝ) ≤ 1 by norm_num)
    have hfloor :
        (liuPanSourceIntervalUpper N : ℝ) ≤ (N : ℝ) := by
      unfold liuPanSourceIntervalUpper
      exact (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)).trans hpow
    exact_mod_cast hfloor
  · intro a _haN ha
    exact Finset.mem_Ioc.mp (liuWeight_support_mem_panSourceInterval hlow ha)

/-- Eventual source-interval identity for every modulus and residue. -/
theorem eventually_liuMainPanCoprimeSum_eq_panSourceInterval
    (main : ℝ → ℝ) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ q l : ℕ,
      liuMainPanCoprimeSum main N N q l
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) =
        liuMainPanCoprimeIntervalSum main N
          (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q l
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
  filter_upwards [eventually_liuPanSourceIntervalLower_lt_liuSourceZ10 B,
    eventually_ge_atTop (1 : ℕ)] with N hlow hN
  intro q l
  exact liuMainPanCoprimeSum_eq_panSourceInterval main hN hlow

/-- The residue-class maximum in the literal source-interval formulation of
Pan--Ding--Wang, Corollary (2.30). -/
noncomputable def liuMainPanCoprimeIntervalMaxL
    (main : ℝ → ℝ) (Y A₁ A₂ q : ℕ) (f : ℕ → ℝ) : ℝ :=
  let S := AnalyticNumberTheory.Sieve.unitResidues q
  if h : S.Nonempty then
    (S.image (fun l => |liuMainPanCoprimeIntervalSum main Y A₁ A₂ q l f|)).max'
      (Finset.image_nonempty.mpr h)
  else 0

/-- The literal left side of Corollary (2.30), instantiated with Liu's source
interval and retaining the paper's strict real modulus cutoff. -/
noncomputable def liuPanWangDingCorollary230Sum
    (κ : ℝ) (N : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panSourceStrictModulusCutoff N B),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
        liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral κ) N
          (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))

/-- Source-faithful Liu specialization of Pan--Ding--Wang, Corollary (2.30).
This is the consequence consumed by the `eqn-r` lane, not a formalization of
the paper's more general arbitrary-`f`, arbitrary-interval statement.  The
additive normalization of `li` is fixed but unspecified by the source, while
the source exponent (the paper permits `B = 2A + 24`) is existentially weakened. -/
def LiuPanWangDingCorollary230 : Prop :=
  ∃ κ_src : ℝ, ∀ A : ℝ, 0 < A →
    ∃ C : ℝ, 0 < C ∧
    ∃ B : ℝ, 0 ≤ B ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      liuPanWangDingCorollary230Sum κ_src N B ≤
        C * N / Real.log N ^ A

private theorem liuMainPanMaxL_eq_intervalMaxL
    (main : ℝ → ℝ) (N A₁ A₂ q : ℕ) (f : ℕ → ℝ)
    (h : ∀ l : ℕ,
      liuMainPanCoprimeSum main N N q l f =
        liuMainPanCoprimeIntervalSum main N A₁ A₂ q l f) :
    liuMainPanMaxL main N N q f =
      liuMainPanCoprimeIntervalMaxL main N A₁ A₂ q f := by
  unfold liuMainPanMaxL liuMainPanCoprimeIntervalMaxL
  dsimp only
  split <;> simp_all only

private theorem liuMainPanEndpointWeightedSum_le_corollary230Sum
    (κ : ℝ) (N : ℕ) (B : ℝ)
    (hinterval : ∀ q l : ℕ,
      liuMainPanCoprimeSum (liuLogarithmicIntegral κ) N N q l
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) =
        liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral κ) N
          (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q l
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)))
    (hcut : range (panModulusCutoff N (B + 1) + 1) ⊆
      range (panSourceStrictModulusCutoff N B)) :
    liuMainPanEndpointWeightedSum (liuLogarithmicIntegral κ) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (B + 1) ≤
      liuPanWangDingCorollary230Sum κ N B := by
  classical
  unfold liuMainPanEndpointWeightedSum liuPanWangDingCorollary230Sum
  calc
    (∑ q ∈ range (panModulusCutoff N (B + 1) + 1),
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
        (3 : ℝ) ^ q.primeFactors.card *
          liuMainPanMaxL (liuLogarithmicIntegral κ) N N q
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) =
      ∑ q ∈ range (panModulusCutoff N (B + 1) + 1),
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
          (3 : ℝ) ^ q.primeFactors.card *
            liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral κ) N
              (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [liuMainPanMaxL_eq_intervalMaxL
          (liuLogarithmicIntegral κ) N
          (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (hinterval q)]
    _ ≤ ∑ q ∈ range (panSourceStrictModulusCutoff N B),
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
          (3 : ℝ) ^ q.primeFactors.card *
            liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral κ) N
              (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hcut
        intro q _ _
        rw [← liuMainPanMaxL_eq_intervalMaxL
          (liuLogarithmicIntegral κ) N
          (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (hinterval q)]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity))
          (liuMainPanMaxL_nonneg (liuLogarithmicIntegral κ) N N q
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)))

/-- The literal source contract transports all the way to Liu's canonical
`κ = 2` coprime consumer.  The source cutoff exponent `B` becomes `B+1` at the
closed-floor endpoint, and the fixed normalization discrepancy is absorbed in
one further copy of `N / log^A N`. -/
theorem LiuPanWangDingCorollary230.to_coprimeRBound
    (hPan : LiuPanWangDingCorollary230)
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
    ∃ B : ℝ, 0 ≤ B ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      LiuPaperQCoprimeRBound (liuLogarithmicIntegral 2) N ε A C := by
  rcases hPan with ⟨κ_src, hPan⟩
  rcases hPan A hA with ⟨Csrc, hCsrc, Bsrc, hBsrc, Nsrc, hsrc⟩
  rcases eventually_atTop.mp
      (eventually_liuMainPanCoprimeSum_eq_panSourceInterval
        (liuLogarithmicIntegral κ_src) Bsrc) with
    ⟨Ninterval, hinterval⟩
  rcases exists_range_panModulusCutoff_add_one_subset_sourceStrict Bsrc with
    ⟨Nstrict, hstrict⟩
  rcases exists_liuSourceDEpsilon_le_panModulusCutoff ε (Bsrc + 1)
      hε (by linarith) with
    ⟨Nconsumer, hconsumer⟩
  have hκsrc : ∀ᶠ N : ℕ in atTop,
      liuPaperQSourceCoprimeDistributionMajorant
          (liuLogarithmicIntegral κ_src) N ε ≤
        Csrc * (N : ℝ) / Real.log N ^ A := by
    filter_upwards [eventually_ge_atTop Nsrc, eventually_ge_atTop Ninterval,
      eventually_ge_atTop Nstrict, eventually_ge_atTop Nconsumer] with
      N hNsrc hNinterval hNstrict hNconsumer
    apply liuPaperQCoprimeRBound_of_liuMainPanEndpointMeanValueAt
      (liuLogarithmicIntegral κ_src) N ε A (Bsrc + 1) Csrc
      (hconsumer N hNconsumer)
    exact (liuMainPanEndpointWeightedSum_le_corollary230Sum
      κ_src N Bsrc (hinterval N hNinterval) (hstrict N hNstrict)).trans
        (hsrc N hNsrc)
  have hcanonical :=
    eventually_liuPaperQSourceCoprimeDistributionMajorant_li_normalization_transfer
      2 κ_src ε A Csrc hε.le hκsrc
  rcases eventually_atTop.mp hcanonical with ⟨Ncanonical, hcanonical⟩
  refine ⟨Csrc + 1, by linarith, Bsrc + 1, by linarith, Ncanonical, ?_⟩
  intro N hN
  exact hcanonical N hN

/-- The exact downstream analytic interface needed after source transport: every
positive `ε,A` admits an eventual canonical-`li₂` coprime `eqn-r` bound. -/
def LiuPanCanonicalCoprimeTheorem : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A →
    ∃ C : ℝ, 0 < C ∧
    ∃ B : ℝ, 0 ≤ B ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      LiuPaperQCoprimeRBound (liuLogarithmicIntegral 2) N ε A C

/-- The literal source corollary supplies the exact canonical consumer
interface, without identifying its unspecified additive normalization with `2`. -/
theorem LiuPanWangDingCorollary230.to_canonicalCoprimeTheorem
    (hPan : LiuPanWangDingCorollary230) : LiuPanCanonicalCoprimeTheorem :=
  fun ε A hε hA ↦ hPan.to_coprimeRBound ε A hε hA

/-- A post-transport endpoint contract at a specified additive normalization.
It is convenient for downstream consumers, but is not the literal statement of
Corollary (2.30): the source-faithful Liu specialization is
`LiuPanWangDingCorollary230`, with a strict modulus cutoff, source interval,
and existential source normalization. -/
def LiuPanWangDingSourceMeanValue (κ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ C : ℝ, 0 < C ∧
    ∃ B : ℝ, 0 ≤ B ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      LiuMainPanEndpointMeanValueAt (liuLogarithmicIntegral κ) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C

/-- A stronger conditional convenience contract at canonical normalization
`li₂(x) = 2 + ∫₂ˣ dt / log t`.  This is not identified definitionally with the
source-literal Corollary (2.30); use
`LiuPanWangDingCorollary230.to_coprimeRBound` for the source-faithful route. -/
def LiuPanWangDingTheorem : Prop :=
  LiuPanWangDingSourceMeanValue 2

/-- The aggregate Pan--Wang--Ding source theorem directly supplies Liu's
source-`Q` coprime remainder bound.  The only additional step is the already
proved eventual inclusion of Liu's divisor cutoff in Pan's modulus range. -/
theorem LiuPanWangDingSourceMeanValue.to_coprimeRBound
    {κ : ℝ} (hPan : LiuPanWangDingSourceMeanValue κ)
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
    ∃ B : ℝ, 0 ≤ B ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      LiuPaperQCoprimeRBound (liuLogarithmicIntegral κ) N ε A C := by
  rcases hPan A hA with ⟨C, hC, B, hB, NPan, hPanN⟩
  rcases exists_liuSourceDEpsilon_le_panModulusCutoff ε B hε hB with
    ⟨NCut, hCut⟩
  refine ⟨C, hC, B, hB, max NPan NCut, ?_⟩
  intro N hN
  rcases max_le_iff.mp hN with ⟨hNPan, hNCut⟩
  exact liuPaperQCoprimeRBound_of_liuMainPanEndpointMeanValueAt
    (liuLogarithmicIntegral κ) N ε A B C
    (hCut N hNCut) (hPanN N hNPan)

/-- Consumer consequence of the stronger conditional canonical contract. -/
theorem LiuPanWangDingTheorem.to_coprimeRBound
    (hPan : LiuPanWangDingTheorem)
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
    ∃ B : ℝ, 0 ≤ B ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      LiuPaperQCoprimeRBound (liuLogarithmicIntegral 2) N ε A C :=
  LiuPanWangDingSourceMeanValue.to_coprimeRBound hPan ε A hε hA

/-- The stronger canonical endpoint contract also supplies the minimal
canonical consumer interface. -/
theorem LiuPanWangDingTheorem.to_canonicalCoprimeTheorem
    (hPan : LiuPanWangDingTheorem) : LiuPanCanonicalCoprimeTheorem :=
  fun ε A hε hA ↦ hPan.to_coprimeRBound ε A hε hA

/-- The canonical coprime consumer interface implies every fixed logarithmic
saving for Liu's exact `eqn-r` source sum.  The full majorant keeps
`3^ω(d)` outside the absolute value of each inner residue-class error. -/
theorem LiuPanCanonicalCoprimeTheorem.eventually_liuPaperQSourceFullDistributionMajorant_le
    (hPan : LiuPanCanonicalCoprimeTheorem)
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      liuPaperQSourceFullDistributionMajorant
          (liuLogarithmicIntegral 2) N ε ≤
        C * N / Real.log N ^ A := by
  rcases hPan ε A hε hA with
    ⟨Cpan, hCpan, _B, _hB, NPan, hPanN⟩
  let CR1 : ℝ :=
    15 * liuLogarithmicIntegralUpperConstant 2 *
      liuSourceR1P₂ReciprocalBound * paperQStyleDivisorWeightLogConstant
  have hCR1 : 0 ≤ CR1 := by
    dsimp [CR1]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (liuLogarithmicIntegralUpperConstant_nonneg 2))
        liuSourceR1P₂ReciprocalBound_nonneg)
      paperQStyleDivisorWeightLogConstant_nonneg
  have hreal : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (A + 2) ≤ x ^ (1 / 10 : ℝ) := by
    have hbound := (isLittleO_log_rpow_rpow_atTop (A + 2)
      (by norm_num : (0 : ℝ) < 1 / 10)).bound (show 0 < (1 : ℝ) by norm_num)
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) _),
      one_mul] at hx
    exact hx
  have hnat : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ (A + 2) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  rcases eventually_atTop.mp hnat with ⟨Nscalar, hscalar⟩
  refine ⟨Cpan + CR1, add_pos_of_pos_of_nonneg hCpan hCR1,
    max NPan (max Nscalar 8), ?_⟩
  intro N hN
  rcases max_le_iff.mp hN with ⟨hNPan, hNrest⟩
  rcases max_le_iff.mp hNrest with ⟨hNscalar, hN8⟩
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hR1scale :
      (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 ≤
        (N : ℝ) / Real.log N ^ A := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogpos A)]
    calc
      ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2) * Real.log N ^ A =
          (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (A + 2) := by
            rw [Real.rpow_add hlogpos, Real.rpow_two]
            ring
      _ ≤ (N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left (hscalar N hNscalar)
          (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num
  calc
    liuPaperQSourceFullDistributionMajorant
          (liuLogarithmicIntegral 2) N ε ≤
        Cpan * N / Real.log N ^ A +
          CR1 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
      simpa [CR1] using
        liuPaperQSourceFullDistributionMajorant_liuLogarithmicIntegral_le
          2 N ε A Cpan hN8 hε.le (hPanN N hNPan)
    _ ≤ Cpan * ((N : ℝ) / Real.log N ^ A) +
          CR1 * ((N : ℝ) / Real.log N ^ A) := by
      rw [show Cpan * (N : ℝ) / Real.log N ^ A =
          Cpan * ((N : ℝ) / Real.log N ^ A) by ring,
        show CR1 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 =
          CR1 * ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2) by ring]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hR1scale hCR1) _
    _ = (Cpan + CR1) * N / Real.log N ^ A := by ring

/-- Backward-compatible wrapper for the stronger canonical endpoint contract. -/
theorem LiuPanWangDingTheorem.eventually_liuPaperQSourceFullDistributionMajorant_le
    (hPan : LiuPanWangDingTheorem)
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      liuPaperQSourceFullDistributionMajorant
          (liuLogarithmicIntegral 2) N ε ≤
        C * N / Real.log N ^ A :=
  hPan.to_canonicalCoprimeTheorem
    |>.eventually_liuPaperQSourceFullDistributionMajorant_le ε A hε hA

/-- Source-faithful wrapper from literal Corollary `(2.30)` to the same full
canonical consumer majorant. -/
theorem LiuPanWangDingCorollary230.eventually_liuPaperQSourceFullDistributionMajorant_le
    (hPan : LiuPanWangDingCorollary230)
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      liuPaperQSourceFullDistributionMajorant
          (liuLogarithmicIntegral 2) N ε ≤
        C * N / Real.log N ^ A :=
  hPan.to_canonicalCoprimeTheorem
    |>.eventually_liuPaperQSourceFullDistributionMajorant_le ε A hε hA

end MathlibNt.SieveTheory.LiuWeight
