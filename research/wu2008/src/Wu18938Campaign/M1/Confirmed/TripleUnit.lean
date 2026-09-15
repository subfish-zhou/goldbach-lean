import Wu18938Campaign.M1.Confirmed.TripleBuchstab
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleUnitNegligible

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Triple

open Wu2008DoubleSieve LowerTripleGroupedFinite Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem residual_square {m i N d : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    ((N : ℝ) ^ (1 / 2 - δ) / d) ^ 2 ≤ (N : ℝ) / d := by
  have hd0 := hb.support_pos hd
  have hR := (hb.support_geometry hN hη hδ hd).2.2.1
  have hl := roughBox_log_geometry hb hN hη hδ hd
  have hphi : 2 ≤ omega3XPhi N d δ := by linarith [hl.2.2.1]
  rw [omega3XPhi,le_div_iff₀ (log_pos hR)] at hphi
  apply (log_le_log_iff (sq_pos_of_pos (lt_trans zero_lt_one hR))
    (div_pos (by positivity) (by exact_mod_cast hd0))).mp
  simpa only [log_pow,Nat.cast_ofNat] using hphi

theorem tuple_product_bound {m i N d : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {j : Fin 6} {t : PrimeTriple} (ht : t ∈ actualPrimeTriples N δ p j d) :
    ((tupleList t).prod : ℝ) ≤ ((N : ℝ) ^ (1 / 2 - δ) / d) ^ (3 / 2 : ℝ) := by
  let R := (N : ℝ) ^ (1 / 2 - δ) / d
  have hR : 0 < R := lt_trans zero_lt_one (hb.support_geometry hN hη hδ hd).2.2.1
  have hc := tuple_cube hb hN hη hδ p hp hs hd ht
  have hcoord (j : Fin 3) : (tupleCoordinates t j : ℝ) ≤ R ^ (1 / 2 : ℝ) := by
    have hj : j.val < (tupleList t).length := by rw [tupleList_length]; exact j.isLt
    have hm : tupleCoordinates t j ∈ tupleList t := by
      simp only [tupleCoordinates,List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    exact ((mem_primesIcc (rpow_nonneg hR.le _)).mp (hc _ hm)).2.2
  have hh := prod_le_prod (s := (univ : Finset (Fin 3)))
    (fun j _ => Nat.cast_nonneg (tupleCoordinates t j)) (fun j _ => hcoord j)
  rw [tupleCoordinates_product,prod_const,card_univ,Fintype.card_fin] at hh
  have heq : (R ^ (1 / 2 : ℝ)) ^ 3 = R ^ (3 / 2 : ℝ) := by
    rw [← rpow_natCast,← rpow_mul hR.le]
    norm_num
  exact hh.trans_eq heq

theorem unit_power {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6)
    (hmass : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (∑ q ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d), 1 / (q : ℝ)) ≤ 5) :
    unitMass N δ Δ V p j ≤ 5 ^ 3 * (N : ℝ) * (N : ℝ) ^ (-η / 2) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have inner (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      (∑ t ∈ actualPrimeTriples N δ p j d, if tupleProduct d t ≤ N then (1 : ℝ) else 0) ≤
      5 ^ 3 * ((N : ℝ) / d) * (N : ℝ) ^ (-η / 2) := by
    let R := (N : ℝ) ^ (1 / 2 - δ) / d
    have hR : 0 < R := lt_trans zero_lt_one (hb.support_geometry hN hη hδ hd).2.2.1
    have hrec := tuple_reciprocal_le (actualPrimeTriples N δ p j d)
      (fun t ht => tuple_cube hb hN hη hδ p hp hs hd ht) (hmass d hd)
    have hpw : R ^ (3 / 2 : ℝ) ≤ ((N : ℝ) / d) * (N : ℝ) ^ (-η / 2) := by
      have heq : R ^ (3 / 2 : ℝ) = R ^ 2 * R ^ (-(1 / 2) : ℝ) := by
        rw [← rpow_two,← rpow_add hR]
        norm_num
      have hn := rpow_le_rpow_of_nonpos
        (rpow_pos_of_pos (by positivity : (0 : ℝ) < N) _) (hb.remaining d hd)
        (by norm_num : (-(1 / 2) : ℝ) ≤ 0)
      rw [← rpow_mul (by positivity : (0 : ℝ) ≤ N)] at hn
      rw [show η * (-(1 / 2)) = -η / 2 by ring] at hn
      rw [heq]
      exact mul_le_mul (residual_square hb hN hη hδ hd) hn
        (rpow_nonneg hR.le _) (by positivity)
    calc
      _ ≤ ∑ t ∈ actualPrimeTriples N δ p j d,
          R ^ (3 / 2 : ℝ) * (1 / ((tupleList t).prod : ℝ)) := by
        apply sum_le_sum
        intro t ht
        have ht0 : 0 < (tupleList t).prod := by
          have hh := tupleProduct_pos (show 0 < 1 by omega) ht
          simpa only [tupleProduct_literal,one_mul] using hh
        have htR : (0 : ℝ) < (tupleList t).prod := by exact_mod_cast ht0
        have hc : (1 : ℝ) ≤ R ^ (3 / 2 : ℝ) / ((tupleList t).prod : ℝ) :=
          (le_div_iff₀ htR).mpr (by
            simpa only [one_mul] using tuple_product_bound hb hN hη hδ p hp hs hd ht)
        calc
          _ ≤ (1 : ℝ) := by split_ifs <;> norm_num
          _ ≤ _ := by simpa only [div_eq_mul_inv,one_mul] using hc
      _ = R ^ (3 / 2 : ℝ) *
          (∑ t ∈ actualPrimeTriples N δ p j d, 1 / ((tupleList t).prod : ℝ)) := by rw [mul_sum]
      _ ≤ R ^ (3 / 2 : ℝ) * 5 ^ 3 := mul_le_mul_of_nonneg_left hrec (rpow_nonneg hR.le _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hpw (by norm_num : (0 : ℝ) ≤ 5 ^ 3)]
  unfold unitMass boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        (5 ^ 3 * ((N : ℝ) / d) * (N : ℝ) ^ (-η / 2)) :=
      mul_le_mul_of_nonneg_left (inner d hd) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem unit_negligible (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ j : Fin 6,
      unitMass N δ Δ V p j ≤ ε * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := roughBox_cube_mass m (δ := δ) hη
  obtain ⟨T1,h1⟩ := eventually_atTop.mp
    ((unit_power_log_decay (half_pos hη)).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 5 ^ 3 by positivity)))
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp hs j
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsmall := (h1 N (by omega)).le
  have hn : (N : ℝ) ^ (-η / 2) ≤ (ε / 5 ^ 3) / log N := by
    apply (le_div_iff₀ hl).mpr
    simpa only [neg_div,mul_comm] using hsmall
  have hu := unit_power hb (by omega) hη hδ p hp hs j (h0 N (by omega) i Δ V hb)
  have hW : 0 ≤ boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
    sum_nonneg (fun _ _ => by positivity)
  apply hu.trans
  calc
    _ ≤ 5 ^ 3 * (N : ℝ) * ((ε / 5 ^ 3) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by gcongr
    _ = _ := by ring

theorem mass_paid (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ j : Fin 6,
      (LowerTripleGrouped.roughFamily N δ Δ V p j).mass ≤
        finiteBuchstabMain N δ Δ V p j +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := mass_paid_nonunit m hη hδ (half_pos he)
  obtain ⟨T1,_,h1⟩ := unit_negligible m hη hδ (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp hs j
  have hn := h0 N (by omega) i Δ V hb p hp hs j
  have hu := h1 N (by omega) i Δ V hb p hp hs j
  linarith only [hn,hu]

end Wu18938Campaign.M1.Confirmed.Triple
