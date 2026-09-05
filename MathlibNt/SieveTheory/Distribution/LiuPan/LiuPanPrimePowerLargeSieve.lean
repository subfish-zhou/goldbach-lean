import AnalyticNumberTheory.LargeSieve.BombieriDavenport
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerCharacters

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace MathlibNt.SieveTheory

open Finset
open AnalyticNumberTheory.LargeSieve

/-- The (ordered) dyadic blocks in the binary decomposition of `[start,start+rem)`.
The recursive call is on the remainder after removing the largest dyadic block. -/
def dyadicPrefixBlocks : ℕ → ℕ → List (ℕ × ℕ)
  | _start, 0 => []
  | start, rem + 1 =>
      let k := Nat.log 2 (rem + 1)
      let p := 2 ^ k
      (start, p) :: dyadicPrefixBlocks (start + p) (rem + 1 - p)
termination_by _ rem => rem
decreasing_by
  have hp : 1 ≤ 2 ^ Nat.log 2 (rem + 1) := by
    simpa using (Nat.one_le_pow' (Nat.log 2 (rem + 1)) 1)
  omega

def dyadicBlockSum {α : Type*} [AddCommMonoid α] (f : ℕ → α) (b : ℕ × ℕ) : α :=
  ∑ n ∈ Finset.Ico b.1 (b.1 + b.2), f n

theorem dyadicPrefixBlocks_sum {α : Type*} [AddCommMonoid α] (f : ℕ → α)
    (start rem : ℕ) :
    ((dyadicPrefixBlocks start rem).map (dyadicBlockSum f)).sum =
      ∑ n ∈ Finset.Ico start (start + rem), f n := by
  induction rem using Nat.strong_induction_on generalizing start with
  | h rem ih =>
      cases rem with
      | zero => simp [dyadicPrefixBlocks]
      | succ rem =>
          let p := 2 ^ Nat.log 2 (rem + 1)
          let rem' := rem + 1 - p
          have hp : p ≤ rem + 1 := by
            dsimp [p]
            exact Nat.pow_log_le_self 2 (by omega)
          have hlt : rem' < rem + 1 := by
            dsimp [rem']
            have hp1 : 1 ≤ p := by
              dsimp [p]
              simpa using (Nat.one_le_pow' (Nat.log 2 (rem + 1)) 1)
            omega
          have hrec := ih rem' hlt (start + p)
          simp only [dyadicPrefixBlocks, List.map_cons, List.sum_cons,
            dyadicBlockSum] at hrec ⊢
          rw [hrec]
          rw [Finset.sum_Ico_consecutive f (by omega) (by omega)]
          dsimp [rem']
          have hsub : rem + 1 - p + p = rem + 1 := Nat.sub_add_cancel hp
          have hend :
              start + p + (rem + 1 - p) = start + (rem + 1) := by
            calc
            start + p + (rem + 1 - p) =
                start + ((rem + 1 - p) + p) := by omega
            _ = start + (rem + 1) := by rw [hsub]
          rw [hend]

theorem dyadicPrefixBlocks_card_le (start rem : ℕ) :
    (dyadicPrefixBlocks start rem).length ≤ 1 + Nat.log 2 rem := by
  induction rem using Nat.strong_induction_on generalizing start with
  | h rem ih =>
      cases rem with
      | zero => simp [dyadicPrefixBlocks]
      | succ rem =>
          let p := 2 ^ Nat.log 2 (rem + 1)
          let rem' := rem + 1 - p
          have hp : p ≤ rem + 1 := by
            dsimp [p]
            exact Nat.pow_log_le_self 2 (by omega)
          have hlt : rem' < rem + 1 := by
            dsimp [rem']
            have hp1 : 1 ≤ p := by
              dsimp [p]
              simpa using (Nat.one_le_pow' (Nat.log 2 (rem + 1)) 1)
            omega
          have hrec := ih rem' hlt (start + p)
          simp only [dyadicPrefixBlocks, List.length_cons] at hrec ⊢
          by_cases hz : rem' = 0
          · simp [hz, rem', p, dyadicPrefixBlocks]
          · have hlog : Nat.log 2 rem' < Nat.log 2 (rem + 1) := by
             apply (Nat.log_lt_iff_lt_pow (by omega) hz).2
             have hupper : rem + 1 < 2 ^ (Nat.log 2 (rem + 1) + 1) :=
               Nat.lt_pow_succ_log_self (by omega) _
             dsimp [rem', p] at hupper ⊢
             rw [pow_succ] at hupper
             dsimp [p, rem'] at *
             omega
            have hrec' :
             (dyadicPrefixBlocks
                 (start + 2 ^ Nat.log 2 (rem + 1))
                 (rem + 1 - 2 ^ Nat.log 2 (rem + 1))).length ≤
               1 + Nat.log 2 (rem + 1 - 2 ^ Nat.log 2 (rem + 1)) := by
             simpa [p, rem'] using hrec
            have hlog' :
             Nat.log 2 (rem + 1 - 2 ^ Nat.log 2 (rem + 1)) <
               Nat.log 2 (rem + 1) := by
             simpa [p, rem'] using hlog
            omega

theorem list_norm_sum_le {α : Type*} [SeminormedAddCommGroup α] (l : List α) :
    ‖l.sum‖ ≤ (l.map norm).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simpa [List.sum_cons, List.map_cons] using
        (norm_add_le x l.sum).trans (by
          simpa [add_comm] using add_le_add_left ih ‖x‖)

theorem list_sq_sum_le (l : List ℝ) :
    l.sum ^ 2 ≤ (l.length : ℝ) * (l.map (fun x => x ^ 2)).sum := by
  let s : Finset (Fin l.length) := Finset.univ
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => l.get i)
  calc
    l.sum ^ 2 ≤ (l.length : ℝ) * (∑ i : Fin l.length, (l.get i) ^ 2) := by
      simpa [s] using h
    _ = (l.length : ℝ) * (l.map (fun x => x ^ 2)).sum := by
      have heq :
          (∑ i : Fin l.length, (l.get i) ^ 2) =
            (l.map (fun x => x ^ 2)).sum := by
        simpa only [List.get_eq_getElem] using
          (Fin.sum_univ_fun_getElem l (fun x : ℝ => x ^ 2))
      rw [heq]

theorem dyadic_prefix_norm_sq_le {α : Type*} [SeminormedAddCommGroup α]
    (f : ℕ → α) (start rem : ℕ) :
    ‖∑ n ∈ Finset.Ico start (start + rem), f n‖ ^ 2 ≤
      (dyadicPrefixBlocks start rem).length *
        (((dyadicPrefixBlocks start rem).map
          (fun b => ‖∑ n ∈ Finset.Ico b.1 (b.1 + b.2), f n‖ ^ 2)).sum) := by
  let bs := dyadicPrefixBlocks start rem
  have hsum := dyadicPrefixBlocks_sum f start rem
  have hnorm := list_norm_sum_le (bs.map (dyadicBlockSum f))
  have hsq := list_sq_sum_le (bs.map (fun b => ‖dyadicBlockSum f b‖))
  rw [← hsum]
  have hnon : 0 ≤ ((bs.map (dyadicBlockSum f)).map norm).sum := by
    induction bs with
    | nil => simp
    | cons b bs ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_nonneg (norm_nonneg _) ih
  have hsqnorm :
      ‖(bs.map (dyadicBlockSum f)).sum‖ ^ 2 ≤
        ((bs.map (dyadicBlockSum f)).map norm).sum ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) hnon).2 hnorm
  calc
    ‖(bs.map (dyadicBlockSum f)).sum‖ ^ 2 ≤
        ((bs.map (dyadicBlockSum f)).map norm).sum ^ 2 := hsqnorm
    _ ≤ (bs.length : ℝ) *
        (((bs.map (dyadicBlockSum f)).map (fun z => ‖z‖ ^ 2)).sum) := by
          simpa [List.map_map, Function.comp_def] using hsq
    _ = (dyadicPrefixBlocks start rem).length *
        (((dyadicPrefixBlocks start rem).map
          (fun b => ‖∑ n ∈ Finset.Ico b.1 (b.1 + b.2), f n‖ ^ 2)).sum) := by
      simp [bs, List.map_map, Function.comp_def, dyadicBlockSum]

theorem sum_divisors_moebius_complex {d : ℕ} :
    (∑ e ∈ d.divisors, (ArithmeticFunction.moebius e : ℂ)) =
      if d = 1 then 1 else 0 := by
  have h : (∑ e ∈ d.divisors, ArithmeticFunction.moebius e) =
      if d = 1 then 1 else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  exact_mod_cast h

/-- Möbius inversion of the coprimality indicator in the coefficient field used
by the character sums. -/
theorem sum_moebius_if_dvd_eq_coprime {r n : ℕ} (hr : r ≠ 0) :
    (∑ e ∈ r.divisors,
      if e ∣ n then (ArithmeticFunction.moebius e : ℂ) else 0) =
      if n.Coprime r then 1 else 0 := by
  rw [← sum_filter]
  have hfilter : {e ∈ r.divisors | e ∣ n} = (n.gcd r).divisors := by
    ext e
    simp [Nat.mem_divisors, hr, Nat.gcd_ne_zero_right hr, Nat.dvd_gcd_iff,
      and_comm]
  rw [hfilter, sum_divisors_moebius_complex]

/-- An induced character is its primitive character times the exact
coprimality indicator for the quotient of its level by its conductor. -/
theorem dirichletCharacter_eq_primitive_mul_coprimeIndicator {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ (n : ZMod q) =
      χ.primitiveCharacter (n : ZMod χ.conductor) *
        (if n.Coprime (q / χ.conductor) then 1 else 0) := by
  have hq : χ.conductor * (q / χ.conductor) = q :=
    Nat.mul_div_cancel' χ.conductor_dvd_level
  by_cases hd : n.Coprime χ.conductor
  · by_cases hr : n.Coprime (q / χ.conductor)
    · have hnq : n.Coprime q := by
        rw [← hq, Nat.coprime_mul_iff_right]
        exact ⟨hd, hr⟩
      rw [if_pos hr]
      simp only [mul_one]
      simpa using
        (χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
          (Nat.isCoprime_iff_coprime.mpr hnq)).symm
    · have hnq : ¬n.Coprime q := by
        rw [← hq, Nat.coprime_mul_iff_right]
        exact fun h => hr h.2
      rw [if_neg hr]
      simp only [mul_zero]
      exact MulChar.map_nonunit χ ((ZMod.isUnit_iff_coprime n q).not.mpr hnq)
  · have hnq : ¬n.Coprime q := by
      rw [← hq, Nat.coprime_mul_iff_right]
      exact fun h => hd h.1
    rw [MulChar.map_nonunit χ ((ZMod.isUnit_iff_coprime n q).not.mpr hnq)]
    rw [MulChar.map_nonunit χ.primitiveCharacter
      ((ZMod.isUnit_iff_coprime n χ.conductor).not.mpr hd)]
    simp

/-- Exact Möbius expansion of the noncoprime correction for an induced
Dirichlet character. -/
theorem dirichletCharacter_eq_primitive_mul_moebius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ (n : ZMod q) =
      χ.primitiveCharacter (n : ZMod χ.conductor) *
        ∑ e ∈ (q / χ.conductor).divisors,
          if e ∣ n then (ArithmeticFunction.moebius e : ℂ) else 0 := by
  rw [dirichletCharacter_eq_primitive_mul_coprimeIndicator]
  rw [sum_moebius_if_dvd_eq_coprime]
  exact (Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
      (DirichletCharacter.conductor_dvd_level χ))
    (Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero χ))).ne'

/-- Reindex a finite sum restricted to multiples of `e` by its quotient. -/
theorem sum_range_ite_dvd {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) {e : ℕ} (he : 0 < e) (y : ℕ) :
    (∑ n ∈ range (y + 1), if e ∣ n then f n else 0) =
      ∑ m ∈ range (y / e + 1), f (e * m) := by
  rw [← sum_filter]
  symm
  refine Finset.sum_bij
    (s := range (y / e + 1))
    (t := {n ∈ range (y + 1) | e ∣ n})
    (f := fun m => f (e * m)) (g := f)
    (fun m _ => e * m) ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_range] at hm
    rw [mem_filter, mem_range]
    constructor
    · rw [Nat.lt_succ_iff] at hm ⊢
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le he).mp hm
    · exact dvd_mul_right e m
  · intro m₁ _ m₂ _ h
    exact Nat.mul_left_cancel he h
  · intro n hn
    rw [mem_filter, mem_range] at hn
    refine ⟨n / e, ?_, Nat.mul_div_cancel' hn.2⟩
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (Nat.le_of_lt_succ hn.1)
  · intro m _
    rfl

/-- Conductor-first transfer for one prefix.  The noncoprime correction is
linearized before any character Cauchy--Schwarz: each divisor `e` dilates the
coefficient sequence and leaves one primitive character sum. -/
theorem characterPrefixSum_eq_sum_primitive_dilations {q : ℕ} [NeZero q]
    (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    (∑ n ∈ range (y + 1), a n * χ (n : ZMod q)) =
      ∑ e ∈ (q / χ.conductor).divisors,
        ((ArithmeticFunction.moebius e : ℂ) *
          χ.primitiveCharacter (e : ZMod χ.conductor)) *
          ∑ m ∈ range (y / e + 1),
            a (e * m) *
              χ.primitiveCharacter (m : ZMod χ.conductor) := by
  calc
    (∑ n ∈ range (y + 1), a n * χ (n : ZMod q)) =
        ∑ n ∈ range (y + 1),
          a n * (χ.primitiveCharacter (n : ZMod χ.conductor) *
            ∑ e ∈ (q / χ.conductor).divisors,
              if e ∣ n then (ArithmeticFunction.moebius e : ℂ) else 0) := by
      apply sum_congr rfl
      intro n _
      rw [dirichletCharacter_eq_primitive_mul_moebius]
    _ = ∑ e ∈ (q / χ.conductor).divisors,
        ∑ n ∈ range (y + 1),
          a n * (χ.primitiveCharacter (n : ZMod χ.conductor) *
            if e ∣ n then (ArithmeticFunction.moebius e : ℂ) else 0) := by
      simp_rw [mul_sum]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro e he
      have hepos : 0 < e := Nat.pos_of_mem_divisors he
      calc
        (∑ n ∈ range (y + 1),
            a n * (χ.primitiveCharacter (n : ZMod χ.conductor) *
              if e ∣ n then (ArithmeticFunction.moebius e : ℂ) else 0)) =
            ∑ n ∈ range (y + 1),
              if e ∣ n then
                (ArithmeticFunction.moebius e : ℂ) *
                  (a n * χ.primitiveCharacter (n : ZMod χ.conductor))
              else 0 := by
          apply sum_congr rfl
          intro n _
          split_ifs <;> ring
        _ = ∑ m ∈ range (y / e + 1),
            (ArithmeticFunction.moebius e : ℂ) *
              (a (e * m) *
                χ.primitiveCharacter ((e * m : ℕ) : ZMod χ.conductor)) :=
          sum_range_ite_dvd
            (fun n => (ArithmeticFunction.moebius e : ℂ) *
              (a n * χ.primitiveCharacter (n : ZMod χ.conductor)))
            hepos y
        _ = _ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro m _
          rw [show ((e * m : ℕ) : ZMod χ.conductor) =
            (e : ZMod χ.conductor) * (m : ZMod χ.conductor) by norm_num]
          rw [map_mul]
          ring

/-- A Dirichlet-character value has norm at most one, including at nonunits. -/
theorem dirichletCharacter_norm_le_one (q : ℕ)
    (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    ‖χ a‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · rw [dirichletChar_norm_unit χ ha]
  · rw [MulChar.map_nonunit χ ha]
    norm_num

/-- The complex cast of the Möbius function has norm at most one. -/
theorem moebius_complex_norm_le_one (e : ℕ) :
    ‖(ArithmeticFunction.moebius e : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- The conductor-first linear transfer for one prefix.  Crucially, the
triangle inequality is taken only after the exact noncoprime Möbius expansion;
no all-character square mean is introduced. -/
theorem characterPrefixSum_norm_le_sum_primitive_dilations
    {q : ℕ} [NeZero q] (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (y : ℕ) :
    ‖∑ n ∈ range (y + 1), a n * χ (n : ZMod q)‖ ≤
      ∑ e ∈ (q / χ.conductor).divisors,
        ‖∑ m ∈ range (y / e + 1),
          a (e * m) *
           χ.primitiveCharacter (m : ZMod χ.conductor)‖ := by
  rw [characterPrefixSum_eq_sum_primitive_dilations]
  calc
    ‖∑ e ∈ (q / χ.conductor).divisors,
        ((ArithmeticFunction.moebius e : ℂ) *
          χ.primitiveCharacter (e : ZMod χ.conductor)) *
          ∑ m ∈ range (y / e + 1),
           a (e * m) *
             χ.primitiveCharacter (m : ZMod χ.conductor)‖ ≤
        ∑ e ∈ (q / χ.conductor).divisors,
          ‖((ArithmeticFunction.moebius e : ℂ) *
           χ.primitiveCharacter (e : ZMod χ.conductor)) *
           ∑ m ∈ range (y / e + 1),
             a (e * m) *
               χ.primitiveCharacter (m : ZMod χ.conductor)‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro e he
      rw [norm_mul]
      apply mul_le_of_le_one_left (norm_nonneg _)
      rw [norm_mul]
      exact (mul_le_mul
        (moebius_complex_norm_le_one e)
        (dirichletCharacter_norm_le_one χ.conductor χ.primitiveCharacter
          (e : ZMod χ.conductor))
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

noncomputable def characterPrefixSquare (a : ℕ → ℂ) (q y : ℕ)
    (χ : DirichletCharacter ℂ q) : ℝ :=
  ‖∑ n ∈ range y, a n * χ (n : ZMod q)‖ ^ 2

noncomputable def characterPrefixSquareMax (a : ℕ → ℂ) (q N : ℕ)
    (χ : DirichletCharacter ℂ q) : ℝ :=
  ((range (N + 1)).image (fun y => characterPrefixSquare a q y χ)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

noncomputable def characterDyadicPrefixEnergy (a : ℕ → ℂ) (q y : ℕ)
    (χ : DirichletCharacter ℂ q) : ℝ :=
  ((dyadicPrefixBlocks 0 y).map (fun b =>
    ‖∑ n ∈ Ico b.1 (b.1 + b.2), a n * χ (n : ZMod q)‖ ^ 2)).sum

noncomputable def characterDyadicPrefixEnergyMax (a : ℕ → ℂ) (q N : ℕ)
    (χ : DirichletCharacter ℂ q) : ℝ :=
  ((range (N + 1)).image (fun y => characterDyadicPrefixEnergy a q y χ)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- The pointwise Rademacher--Menshov reduction.  Unlike a maximum taken after
the character average, this keeps the prefix maximum inside each primitive
character summand, which is the form needed for conductor regrouping. -/
theorem characterPrefixSquareMax_le_dyadic (a : ℕ → ℂ) (q N : ℕ)
    (χ : DirichletCharacter ℂ q) :
    characterPrefixSquareMax a q N χ ≤
      ((1 + Nat.log 2 (N + 1) : ℕ) : ℝ) *
        characterDyadicPrefixEnergyMax a q N χ := by
  classical
  unfold characterPrefixSquareMax
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := Nat.le_of_lt_succ (mem_range.mp hy)
  have hdy := dyadic_prefix_norm_sq_le
    (fun n => a n * χ (n : ZMod q)) 0 y
  have hdy' :
      characterPrefixSquare a q y χ ≤
        ((dyadicPrefixBlocks 0 y).length : ℝ) *
          characterDyadicPrefixEnergy a q y χ := by
    simpa [characterPrefixSquare, characterDyadicPrefixEnergy] using hdy
  have hcardNat :
      (dyadicPrefixBlocks 0 y).length ≤ 1 + Nat.log 2 (N + 1) := by
    exact (dyadicPrefixBlocks_card_le 0 y).trans
      (Nat.add_le_add_left (Nat.log_mono_right (by omega)) 1)
  have hcard :
      ((dyadicPrefixBlocks 0 y).length : ℝ) ≤
        ((1 + Nat.log 2 (N + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have henergyNonneg : 0 ≤ characterDyadicPrefixEnergy a q y χ := by
    unfold characterDyadicPrefixEnergy
    induction dyadicPrefixBlocks 0 y with
    | nil => simp
    | cons b bs ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_nonneg (sq_nonneg _) ih
  have henergyMax :
      characterDyadicPrefixEnergy a q y χ ≤
        characterDyadicPrefixEnergyMax a q N χ := by
    unfold characterDyadicPrefixEnergyMax
    have hmem :
        characterDyadicPrefixEnergy a q y χ ∈
          (range (N + 1)).image
            (fun z => characterDyadicPrefixEnergy a q z χ) :=
      mem_image.mpr
        ⟨y, mem_range.mpr (Nat.lt_succ_iff.mpr hyN), rfl⟩
    exact le_max' _ _ hmem
  calc
    characterPrefixSquare a q y χ ≤
        ((dyadicPrefixBlocks 0 y).length : ℝ) *
          characterDyadicPrefixEnergy a q y χ := hdy'
    _ ≤ ((1 + Nat.log 2 (N + 1) : ℕ) : ℝ) *
          characterDyadicPrefixEnergy a q y χ :=
      mul_le_mul_of_nonneg_right hcard henergyNonneg
    _ ≤ ((1 + Nat.log 2 (N + 1) : ℕ) : ℝ) *
          characterDyadicPrefixEnergyMax a q N χ :=
      mul_le_mul_of_nonneg_left henergyMax (Nat.cast_nonneg _)

noncomputable def primitiveCharacterPrefixMaxMean
    (Q : ℕ) (a : ℕ → ℂ) (N : ℕ) : ℝ :=
  by
    classical
    exact ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => χ.IsPrimitive),
        characterPrefixSquareMax a q N χ

noncomputable def primitiveCharacterDyadicMaxMean
    (Q : ℕ) (a : ℕ → ℂ) (N : ℕ) : ℝ :=
  by
    classical
    exact ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => χ.IsPrimitive),
        characterDyadicPrefixEnergyMax a q N χ

/-- Exact primitive-character maximal reduction with the prefix maximum inside
the character sum and the original `q / φ(q)` weight unchanged. -/
theorem primitiveCharacterPrefixMaxMean_le_dyadic
    (Q : ℕ) (a : ℕ → ℂ) (N : ℕ) :
    primitiveCharacterPrefixMaxMean Q a N ≤
      ((1 + Nat.log 2 (N + 1) : ℕ) : ℝ) *
        primitiveCharacterDyadicMaxMean Q a N := by
  classical
  unfold primitiveCharacterPrefixMaxMean primitiveCharacterDyadicMaxMean
  conv_rhs => rw [mul_sum]
  apply sum_le_sum
  intro q hq
  have hsum :
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => χ.IsPrimitive),
        characterPrefixSquareMax a q N χ) ≤
        ((1 + Nat.log 2 (N + 1) : ℕ) : ℝ) *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
              (fun χ => χ.IsPrimitive),
            characterDyadicPrefixEnergyMax a q N χ := by
    conv_rhs => rw [mul_sum]
    apply sum_le_sum
    intro χ hχ
    exact characterPrefixSquareMax_le_dyadic a q N χ
  calc
    ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => χ.IsPrimitive),
          characterPrefixSquareMax a q N χ) ≤
      ((q : ℝ) / (q.totient : ℝ)) *
        (((1 + Nat.log 2 (N + 1) : ℕ) : ℝ) *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
              (fun χ => χ.IsPrimitive),
            characterDyadicPrefixEnergyMax a q N χ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((1 + Nat.log 2 (N + 1) : ℕ) : ℝ) *
        (((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
              (fun χ => χ.IsPrimitive),
            characterDyadicPrefixEnergyMax a q N χ) := by ring

/-- Extend a sequence on the naturals by zero to the integers.  This is the
coefficient interface required by `bombieriDavenport_le`. -/
noncomputable def natZeroExtension (a : ℕ → ℂ) : ℤ → ℂ :=
  fun z => if 0 ≤ z then a z.toNat else 0

theorem natZeroExtension_block_sum (a : ℕ → ℂ) (start len q : ℕ)
    (χ : DirichletCharacter ℂ q) :
    (∑ z ∈ Icc ((start : ℤ) - 1 + 1) ((start : ℤ) - 1 + len),
      natZeroExtension a z * χ (z : ZMod q)) =
      ∑ n ∈ Ico start (start + len), a n * χ (n : ZMod q) := by
  classical
  rw [show (start : ℤ) - 1 + 1 = start by omega]
  rw [show (start : ℤ) - 1 + len = start + len - 1 by ring]
  symm
  refine Finset.sum_bij
    (s := Ico start (start + len)) (t := Icc (start : ℤ) (start + len - 1))
    (f := fun n => a n * χ (n : ZMod q))
    (g := fun z => natZeroExtension a z * χ (z : ZMod q))
    (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    rw [mem_Ico] at hn
    rw [mem_Icc]
    constructor <;> omega
  · intro n₁ _ n₂ _ h
    exact Int.natCast_inj.mp h
  · intro z hz
    rw [mem_Icc] at hz
    have hz0 : 0 ≤ z := by omega
    refine ⟨z.toNat, ?_, Int.toNat_of_nonneg hz0⟩
    rw [mem_Ico]
    constructor
    · apply Int.ofNat_le.mp
      rw [Int.toNat_of_nonneg hz0]
      exact hz.1
    · apply Int.ofNat_lt.mp
      rw [Int.toNat_of_nonneg hz0]
      norm_num
      omega
  · intro n _
    simp [natZeroExtension]

theorem natZeroExtension_block_norm_sq_sum (a : ℕ → ℂ) (start len : ℕ) :
    (∑ z ∈ Icc ((start : ℤ) - 1 + 1) ((start : ℤ) - 1 + len),
      ‖natZeroExtension a z‖ ^ 2) =
      ∑ n ∈ Ico start (start + len), ‖a n‖ ^ 2 := by
  classical
  rw [show (start : ℤ) - 1 + 1 = start by omega]
  rw [show (start : ℤ) - 1 + len = start + len - 1 by ring]
  symm
  refine Finset.sum_bij
    (s := Ico start (start + len)) (t := Icc (start : ℤ) (start + len - 1))
    (f := fun n => ‖a n‖ ^ 2) (g := fun z => ‖natZeroExtension a z‖ ^ 2)
    (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    rw [mem_Ico] at hn
    rw [mem_Icc]
    constructor <;> omega
  · intro n₁ _ n₂ _ h
    exact Int.natCast_inj.mp h
  · intro z hz
    rw [mem_Icc] at hz
    have hz0 : 0 ≤ z := by omega
    refine ⟨z.toNat, ?_, Int.toNat_of_nonneg hz0⟩
    rw [mem_Ico]
    constructor
    · apply Int.ofNat_le.mp
      rw [Int.toNat_of_nonneg hz0]
      exact hz.1
    · apply Int.ofNat_lt.mp
      rw [Int.toNat_of_nonneg hz0]
      norm_num
      omega
  · intro n _
    simp [natZeroExtension]

/-- Bombieri--Davenport on one natural-number block, retaining exactly the
original primitive-character and `q / φ(q)` weights. -/
theorem primitiveCharacterBlockMean_le_largeSieve
    (Q : ℕ) (hQ : 0 < Q) (a : ℕ → ℂ) (start len : ℕ) : by
    classical
    exact
      (∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
            (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Ico start (start + len), a n * χ (n : ZMod q)‖ ^ 2) ≤
        largeSieveBound len (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ Ico start (start + len), ‖a n‖ ^ 2 := by
  classical
  have h := bombieriDavenport_le Q hQ (natZeroExtension a) ((start : ℤ) - 1) len
  simpa only [natZeroExtension_block_sum, natZeroExtension_block_norm_sq_sum] using h

/-- The adjacent aligned blocks of a fixed length partition their union. -/
theorem dyadicAlignedBlocks_sum {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (p J : ℕ) :
    ∑ j ∈ range J, ∑ n ∈ Ico (j * p) ((j + 1) * p), f n =
      ∑ n ∈ range (J * p), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      exact sum_range_add_sum_Ico f
        (Nat.mul_le_mul_right p (Nat.le_succ J))

/-- At a fixed aligned dyadic scale, every coefficient energy is charged at
most once. -/
theorem dyadicAlignedBlocks_energy_le (a : ℕ → ℂ) (N p : ℕ) :
    ∑ j ∈ range ((N + 1) / p),
      ∑ n ∈ Ico (j * p) ((j + 1) * p), ‖a n‖ ^ 2 ≤
        ∑ n ∈ range (N + 1), ‖a n‖ ^ 2 := by
  rw [dyadicAlignedBlocks_sum]
  apply sum_le_sum_of_subset_of_nonneg
  · exact range_subset_range.mpr (Nat.div_mul_le_self _ _)
  · intro _ _ _
    positivity

theorem largeSieveBound_mono_length (u v : ℕ) (δ : ℝ) (h : u ≤ v) :
    largeSieveBound u δ ≤ largeSieveBound v δ := by
  unfold largeSieveBound
  have h' : (u : ℝ) ≤ v := by exact_mod_cast h
  linarith

/-- The primitive-character square mean over all aligned blocks at one scale.
The coefficient energy occurs only once, rather than once for every prefix. -/
theorem primitiveCharacterAlignedDyadicBlockMean_le
    (Q : ℕ) (hQ : 0 < Q) (a : ℕ → ℂ) (N p : ℕ) (hp : p ≤ N + 1) : by
    classical
    exact
      (∑ j ∈ range ((N + 1) / p),
        ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
              (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Ico (j * p) ((j + 1) * p),
              a n * χ (n : ZMod q)‖ ^ 2) ≤
        largeSieveBound (N + 1) (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ range (N + 1), ‖a n‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ j ∈ range ((N + 1) / p),
        largeSieveBound (N + 1) (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ Ico (j * p) ((j + 1) * p), ‖a n‖ ^ 2 := by
      apply sum_le_sum
      intro j _
      calc
        _ ≤ largeSieveBound p (1 / (Q : ℝ) ^ 2) *
            ∑ n ∈ Ico (j * p) ((j + 1) * p), ‖a n‖ ^ 2 := by
          simpa [Nat.add_mul] using primitiveCharacterBlockMean_le_largeSieve
            Q hQ a (j * p) p
        _ ≤ largeSieveBound (N + 1) (1 / (Q : ℝ) ^ 2) *
            ∑ n ∈ Ico (j * p) ((j + 1) * p), ‖a n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (largeSieveBound_mono_length p (N + 1) _ hp) (by positivity)
    _ = largeSieveBound (N + 1) (1 / (Q : ℝ) ^ 2) *
        ∑ j ∈ range ((N + 1) / p),
          ∑ n ∈ Ico (j * p) ((j + 1) * p), ‖a n‖ ^ 2 := by
      rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (dyadicAlignedBlocks_energy_le a N p)
      (largeSieveBound_nonneg _ (by positivity))

/-- Summing the aligned block estimate through the binary scales costs just one
fixed logarithmic factor. -/
theorem primitiveCharacterAlignedDyadicMean_le
    (Q : ℕ) (hQ : 0 < Q) (a : ℕ → ℂ) (N : ℕ) : by
    classical
    exact
      (∑ k ∈ range (1 + Nat.log 2 (N + 1)),
        ∑ j ∈ range ((N + 1) / 2 ^ k),
          ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
                (fun χ => χ.IsPrimitive),
              ‖∑ n ∈ Ico (j * 2 ^ k) ((j + 1) * 2 ^ k),
                a n * χ (n : ZMod q)‖ ^ 2) ≤
        ((1 + Nat.log 2 (N + 1) : ℕ) : ℝ) *
          (largeSieveBound (N + 1) (1 / (Q : ℝ) ^ 2) *
            ∑ n ∈ range (N + 1), ‖a n‖ ^ 2) := by
  classical
  calc
    _ ≤ ∑ _ ∈ range (1 + Nat.log 2 (N + 1)),
        largeSieveBound (N + 1) (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ range (N + 1), ‖a n‖ ^ 2 := by
      apply sum_le_sum
      intro k hk
      have hk' : k ≤ Nat.log 2 (N + 1) := by
        have : k < 1 + Nat.log 2 (N + 1) := mem_range.mp hk
        omega
      have hp : 2 ^ k ≤ N + 1 :=
        (Nat.pow_le_pow_right (by omega : 0 < 2) hk').trans
          (Nat.pow_log_le_self 2 (by omega))
      exact primitiveCharacterAlignedDyadicBlockMean_le Q hQ a N (2 ^ k) hp
    _ = _ := by simp

/-- Every block in the recursive decomposition starts no earlier than the
left endpoint of the interval being decomposed. -/
theorem dyadicPrefixBlocks_start_le (start rem : ℕ) (b : ℕ × ℕ)
    (hb : b ∈ dyadicPrefixBlocks start rem) : start ≤ b.1 := by
  induction rem using Nat.strong_induction_on generalizing start b with
  | h rem ih =>
      cases rem with
      | zero => simp [dyadicPrefixBlocks] at hb
      | succ r =>
          let p := 2 ^ Nat.log 2 (r + 1)
          let rem' := r + 1 - p
          have hp1 : 1 ≤ p := by
            dsimp [p]
            simpa using (Nat.one_le_pow' (Nat.log 2 (r + 1)) 1)
          have hlt : rem' < r + 1 := by
            dsimp [rem']
            omega
          simp only [dyadicPrefixBlocks, List.mem_cons] at hb
          rcases hb with h | h
          · subst b
            exact Nat.le_refl _
          · exact (Nat.le_add_right start p).trans
              (ih rem' hlt (start + p) b h)

theorem dyadicPrefixBlocks_nodup (start rem : ℕ) :
    (dyadicPrefixBlocks start rem).Nodup := by
  induction rem using Nat.strong_induction_on generalizing start with
  | h rem ih =>
      cases rem with
      | zero => simp [dyadicPrefixBlocks]
      | succ r =>
          let p := 2 ^ Nat.log 2 (r + 1)
          let rem' := r + 1 - p
          have hp1 : 1 ≤ p := by
            dsimp [p]
            simpa using (Nat.one_le_pow' (Nat.log 2 (r + 1)) 1)
          have hlt : rem' < r + 1 := by
            dsimp [rem']
            omega
          simp only [dyadicPrefixBlocks, List.nodup_cons]
          constructor
          · intro hmem
            have hle := dyadicPrefixBlocks_start_le (start + p) rem'
              (start, p) hmem
            omega
          · exact ih rem' hlt (start + p)

/-- Alignment, scale control, and containment in the original interval for
each recursively selected dyadic block. -/
theorem dyadicPrefixBlocks_aligned_aux (rem K start : ℕ)
    (hstart : 2 ^ K ∣ start) (hlog : Nat.log 2 rem ≤ K)
    (b : ℕ × ℕ) (hb : b ∈ dyadicPrefixBlocks start rem) :
    ∃ k ≤ K, b.2 = 2 ^ k ∧ 2 ^ k ∣ b.1 ∧ b.1 + b.2 ≤ start + rem := by
  induction rem using Nat.strong_induction_on generalizing K start b with
  | h rem ih =>
      cases rem with
      | zero => simp [dyadicPrefixBlocks] at hb
      | succ r =>
          let k0 := Nat.log 2 (r + 1)
          let p := 2 ^ k0
          let rem' := r + 1 - p
          have hp : p ≤ r + 1 := by
            dsimp [p, k0]
            exact Nat.pow_log_le_self 2 (by omega)
          have hp1 : 1 ≤ p := by
            dsimp [p]
            simpa using (Nat.one_le_pow' k0 1)
          have hlt : rem' < r + 1 := by
            dsimp [rem']
            omega
          have hk0 : k0 ≤ K := by simpa [k0] using hlog
          have hstartp : 2 ^ k0 ∣ start :=
            dvd_trans (Nat.pow_dvd_pow 2 hk0) hstart
          have hstarttail : 2 ^ k0 ∣ start + p := by
            apply Nat.dvd_add hstartp
            simp [p]
          have hrem' : Nat.log 2 rem' ≤ k0 := by
            by_cases hz : rem' = 0
            · simp [hz]
            · apply Nat.le_of_lt
              apply (Nat.log_lt_iff_lt_pow (by omega) hz).mpr
              have hu : r + 1 < 2 ^ (Nat.log 2 (r + 1) + 1) :=
                Nat.lt_pow_succ_log_self (by omega) (r + 1)
              have hupper : r + 1 < p + p := by
                calc
                  r + 1 < 2 ^ (Nat.log 2 (r + 1) + 1) := hu
                  _ = p + p := by
                    dsimp [p, k0]
                    rw [pow_succ]
                    ring
              change rem' < p
              have hsub : rem' + p = r + 1 := Nat.sub_add_cancel hp
              omega
          simp only [dyadicPrefixBlocks, List.mem_cons] at hb
          rcases hb with hhead | htail
          · subst b
            refine ⟨k0, hk0, rfl, hstartp, ?_⟩
            change start + p ≤ start + (r + 1)
            omega
          · obtain ⟨k, hk, hlen, hdiv, hend⟩ :=
              ih rem' hlt k0 (start + p) hstarttail hrem' b htail
            refine ⟨k, hk.trans hk0, hlen, hdiv, ?_⟩
            have hsub : rem' + p = r + 1 := Nat.sub_add_cancel hp
            omega

theorem dyadicPrefixBlocks_aligned (y : ℕ) (b : ℕ × ℕ)
    (hb : b ∈ dyadicPrefixBlocks 0 y) :
    ∃ k ≤ Nat.log 2 y, b.2 = 2 ^ k ∧ 2 ^ k ∣ b.1 ∧ b.1 + b.2 ≤ y := by
  simpa using dyadicPrefixBlocks_aligned_aux y (Nat.log 2 y) 0
    (by simp) (by rfl) b hb

noncomputable def alignedDyadicBlockIndices (N : ℕ) :
    Finset (Sigma fun _ : ℕ => ℕ) :=
  (range (1 + Nat.log 2 (N + 1))).sigma
    (fun k => range ((N + 1) / 2 ^ k))

noncomputable def alignedDyadicBlockEmbedding :
    (Sigma fun _ : ℕ => ℕ) ↪ ℕ × ℕ where
  toFun x := (x.2 * 2 ^ x.1, 2 ^ x.1)
  inj' := by
    rintro ⟨k, j⟩ ⟨l, i⟩ h
    have hp : 2 ^ k = 2 ^ l := congrArg Prod.snd h
    have hkl : k = l := Nat.pow_right_injective (by omega) hp
    cases hkl
    have hji : j * 2 ^ k = i * 2 ^ k := congrArg Prod.fst h
    have hji' : j = i :=
      Nat.eq_of_mul_eq_mul_right (by positivity) hji
    cases hji'
    rfl

theorem dyadicPrefixBlock_mem_alignedDyadicBlockIndices
    (N y : ℕ) (hy : y ≤ N) (b : ℕ × ℕ)
    (hb : b ∈ dyadicPrefixBlocks 0 y) :
    ∃ x ∈ alignedDyadicBlockIndices N, alignedDyadicBlockEmbedding x = b := by
  obtain ⟨k, hk, hlen, hdiv, hend⟩ := dyadicPrefixBlocks_aligned y b hb
  have hlog : Nat.log 2 y ≤ Nat.log 2 (N + 1) :=
    Nat.log_mono_right (by omega)
  refine ⟨⟨k, b.1 / 2 ^ k⟩, ?_, ?_⟩
  · unfold alignedDyadicBlockIndices
    rw [mem_sigma]
    constructor
    · apply mem_range.mpr
      change k < 1 + Nat.log 2 (N + 1)
      omega
    · apply mem_range.mpr
      apply (Nat.lt_div_iff_mul_lt (by positivity : 0 < 2 ^ k)).mpr
      rw [Nat.div_mul_cancel hdiv]
      have hbound : b.1 + 2 ^ k ≤ N := by
        rw [← hlen]
        omega
      omega
  · apply Prod.ext
    · change b.1 / 2 ^ k * 2 ^ k = b.1
      exact Nat.div_mul_cancel hdiv
    · change 2 ^ k = b.2
      exact hlen.symm

theorem alignedDyadicBlockIndices_sum (N : ℕ) (f : ℕ × ℕ → ℝ) :
    ∑ b ∈ (alignedDyadicBlockIndices N).map alignedDyadicBlockEmbedding, f b =
      ∑ k ∈ range (1 + Nat.log 2 (N + 1)),
        ∑ j ∈ range ((N + 1) / 2 ^ k), f (j * 2 ^ k, 2 ^ k) := by
  rw [Finset.sum_map]
  unfold alignedDyadicBlockIndices
  rw [Finset.sum_sigma]
  rfl

theorem characterDyadicPrefixEnergy_le_aligned
    (a : ℕ → ℂ) (q N y : ℕ) (χ : DirichletCharacter ℂ q) (hy : y ≤ N) :
    characterDyadicPrefixEnergy a q y χ ≤
      ∑ b ∈ (alignedDyadicBlockIndices N).map alignedDyadicBlockEmbedding,
        ‖∑ n ∈ Ico b.1 (b.1 + b.2), a n * χ (n : ZMod q)‖ ^ 2 := by
  classical
  unfold characterDyadicPrefixEnergy
  rw [← List.sum_toFinset _ (dyadicPrefixBlocks_nodup 0 y)]
  apply sum_le_sum_of_subset_of_nonneg
  · intro b hb
    rw [List.mem_toFinset] at hb
    obtain ⟨x, hx, hxb⟩ :=
      dyadicPrefixBlock_mem_alignedDyadicBlockIndices N y hy b hb
    rw [mem_map]
    exact ⟨x, hx, hxb⟩
  · intro _ _ _
    positivity

theorem characterDyadicPrefixEnergyMax_le_aligned
    (a : ℕ → ℂ) (q N : ℕ) (χ : DirichletCharacter ℂ q) :
    characterDyadicPrefixEnergyMax a q N χ ≤
      ∑ b ∈ (alignedDyadicBlockIndices N).map alignedDyadicBlockEmbedding,
        ‖∑ n ∈ Ico b.1 (b.1 + b.2), a n * χ (n : ZMod q)‖ ^ 2 := by
  classical
  unfold characterDyadicPrefixEnergyMax
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  exact characterDyadicPrefixEnergy_le_aligned a q N y χ
    (Nat.le_of_lt_succ (mem_range.mp hy))

theorem primitiveCharacterDyadicMaxMean_le_alignedIndices
    (Q : ℕ) (a : ℕ → ℂ) (N : ℕ) : by
    classical
    exact
      primitiveCharacterDyadicMaxMean Q a N ≤
        ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
              (fun χ => χ.IsPrimitive),
            ∑ b ∈ (alignedDyadicBlockIndices N).map alignedDyadicBlockEmbedding,
              ‖∑ n ∈ Ico b.1 (b.1 + b.2), a n * χ (n : ZMod q)‖ ^ 2 := by
  classical
  unfold primitiveCharacterDyadicMaxMean
  apply sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left
  · apply sum_le_sum
    intro χ _
    exact characterDyadicPrefixEnergyMax_le_aligned a q N χ
  · positivity

theorem dependent_sum_comm {α γ δ : Type*} {β : α → Type*} [AddCommMonoid δ]
    (s : Finset α) (t : (a : α) → Finset (β a)) (u : Finset γ)
    (f : (a : α) → β a → γ → δ) :
    (∑ a ∈ s, ∑ b ∈ t a, ∑ c ∈ u, f a b c) =
      ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t a, f a b c := by
  classical
  calc
    _ = ∑ x ∈ s.sigma t, ∑ c ∈ u, f x.1 x.2 c := by
      rw [Finset.sum_sigma]
    _ = ∑ c ∈ u, ∑ x ∈ s.sigma t, f x.1 x.2 c := by
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [Finset.sum_sigma]

/-- The existing dyadic-prefix maximum is controlled by the aligned block
family.  The latter has one copy of the coefficient energy at each scale. -/
theorem primitiveCharacterDyadicMaxMean_le_aligned
    (Q : ℕ) (a : ℕ → ℂ) (N : ℕ) : by
    classical
    exact
      primitiveCharacterDyadicMaxMean Q a N ≤
        ∑ k ∈ range (1 + Nat.log 2 (N + 1)),
          ∑ j ∈ range ((N + 1) / 2 ^ k),
            ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
              ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
                  (fun χ => χ.IsPrimitive),
                ‖∑ n ∈ Ico (j * 2 ^ k) ((j + 1) * 2 ^ k),
                  a n * χ (n : ZMod q)‖ ^ 2 := by
  classical
  let s := Icc 1 Q
  let t := fun q : ℕ =>
    (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)
  let u := (alignedDyadicBlockIndices N).map alignedDyadicBlockEmbedding
  let F := fun (q : ℕ) (χ : DirichletCharacter ℂ q) (b : ℕ × ℕ) =>
    ‖∑ n ∈ Ico b.1 (b.1 + b.2), a n * χ (n : ZMod q)‖ ^ 2
  calc
    primitiveCharacterDyadicMaxMean Q a N ≤
        ∑ q ∈ s, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ t q, ∑ b ∈ u, F q χ b := by
      simpa [s, t, u, F] using
        primitiveCharacterDyadicMaxMean_le_alignedIndices Q a N
    _ = ∑ b ∈ u, ∑ q ∈ s, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ t q, F q χ b := by
      calc
        _ = ∑ q ∈ s, ∑ χ ∈ t q, ∑ b ∈ u,
            ((q : ℝ) / (q.totient : ℝ)) * F q χ b := by
              simp_rw [Finset.mul_sum]
        _ = ∑ b ∈ u, ∑ q ∈ s, ∑ χ ∈ t q,
            ((q : ℝ) / (q.totient : ℝ)) * F q χ b :=
              dependent_sum_comm s t u
                (fun q χ b => ((q : ℝ) / (q.totient : ℝ)) * F q χ b)
        _ = _ := by simp_rw [Finset.mul_sum]
    _ = _ := by
      simpa [s, t, u, F, Nat.add_mul] using
        alignedDyadicBlockIndices_sum N
          (fun b => ∑ q ∈ s, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ t q, F q χ b)

/-- End-to-end maximal Bombieri--Davenport estimate for natural coefficients.
The two fixed logarithmic factors respectively come from the prefix
Rademacher--Menshov reduction and the aligned dyadic scales. -/
theorem primitiveCharacterPrefixMaxMean_le_largeSieve
    (Q : ℕ) (hQ : 0 < Q) (a : ℕ → ℂ) (N : ℕ) :
    primitiveCharacterPrefixMaxMean Q a N ≤
      ((1 + Nat.log 2 (N + 1) : ℕ) : ℝ) ^ 2 *
        (largeSieveBound (N + 1) (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ range (N + 1), ‖a n‖ ^ 2) := by
  let L : ℝ := ((1 + Nat.log 2 (N + 1) : ℕ) : ℝ)
  let B : ℝ := largeSieveBound (N + 1) (1 / (Q : ℝ) ^ 2) *
    ∑ n ∈ range (N + 1), ‖a n‖ ^ 2
  have hdyadic : primitiveCharacterDyadicMaxMean Q a N ≤ L * B := by
    simpa [L, B] using
      (primitiveCharacterDyadicMaxMean_le_aligned Q a N).trans
        (primitiveCharacterAlignedDyadicMean_le Q hQ a N)
  calc
    primitiveCharacterPrefixMaxMean Q a N ≤ L * primitiveCharacterDyadicMaxMean Q a N := by
      simpa [L] using primitiveCharacterPrefixMaxMean_le_dyadic Q a N
    _ ≤ L * (L * B) :=
      mul_le_mul_of_nonneg_left hdyadic (by dsimp [L]; positivity)
    _ = L ^ 2 * B := by ring

/-- Truncating a coefficient sequence at the largest index used by a prefix
maximum does not change that maximum. -/
theorem characterPrefixSquareMax_truncate (a : ℕ → ℂ) (q N : ℕ)
    (χ : DirichletCharacter ℂ q) :
    characterPrefixSquareMax (fun n => if n < N then a n else 0) q N χ =
      characterPrefixSquareMax a q N χ := by
  unfold characterPrefixSquareMax
  have himage :
      (range (N + 1)).image (fun y =>
        characterPrefixSquare (fun n => if n < N then a n else 0) q y χ) =
      (range (N + 1)).image (fun y => characterPrefixSquare a q y χ) := by
    apply image_congr
    intro y hy
    unfold characterPrefixSquare
    apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
    apply sum_congr rfl
    intro n hn
    simp only [show n < N from
      lt_of_lt_of_le (mem_range.mp hn) (Nat.le_of_lt_succ (mem_range.mp hy)),
      if_true]
  simp only [himage]

/-- The maximal large sieve only charges coefficients actually occurring in its
prefixes; the apparent final endpoint in the aligned-block proof is removable
by truncation. -/
theorem primitiveCharacterPrefixMaxMean_le_largeSieve_exact
    (Q : ℕ) (hQ : 0 < Q) (a : ℕ → ℂ) (N : ℕ) :
    primitiveCharacterPrefixMaxMean Q a N ≤
      ((1 + Nat.log 2 (N + 1) : ℕ) : ℝ) ^ 2 *
        (largeSieveBound (N + 1) (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ range N, ‖a n‖ ^ 2) := by
  let aN : ℕ → ℂ := fun n => if n < N then a n else 0
  have hmean : primitiveCharacterPrefixMaxMean Q aN N =
      primitiveCharacterPrefixMaxMean Q a N := by
    unfold primitiveCharacterPrefixMaxMean
    apply sum_congr rfl
    intro q hq
    congr 1
    apply sum_congr rfl
    intro χ hχ
    exact characterPrefixSquareMax_truncate a q N χ
  have henergy : (∑ n ∈ range (N + 1), ‖aN n‖ ^ 2) =
      ∑ n ∈ range N, ‖a n‖ ^ 2 := by
    rw [Finset.sum_range_succ]
    simp only [aN, lt_self_iff_false, if_false, norm_zero, pow_two, zero_mul,
      add_zero]
    apply sum_congr rfl
    intro n hn
    simp only [mem_range.mp hn, if_true]
  have h := primitiveCharacterPrefixMaxMean_le_largeSieve Q hQ aN N
  rw [hmean, henergy] at h
  exact h

/-- At square-root conductor range, the explicit weak large-sieve constant costs
only one logarithm. -/
theorem largeSieveBound_le_mul_log_of_sq_le
    (N Q : ℕ) (hN : 1 ≤ N) (hQ : 0 < Q) (hQsq : Q ^ 2 ≤ N) :
    largeSieveBound (N + 2) (1 / (Q : ℝ) ^ 2) ≤
      (17 + 4 / Real.log 2) * N * Real.log (N + 2 : ℕ) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hQN : Q ≤ N := by
    calc
      Q = Q * 1 := by simp
      _ ≤ Q * Q := Nat.mul_le_mul_left Q hQ
      _ = Q ^ 2 := by simp [pow_two]
      _ ≤ N := hQsq
  have hlogQN : Real.log (Q : ℝ) ≤ Real.log (N + 2 : ℕ) :=
    Real.log_le_log hQr (by exact_mod_cast (show Q ≤ N + 2 by omega))
  have hlogN : 1 ≤ Real.log (N + 2 : ℕ) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    exact Real.exp_one_lt_three.le.trans
      (by exact_mod_cast (show 3 ≤ N + 2 by omega))
  have hQsqone : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith
  have hx0 : 0 ≤ Real.log ((Q : ℝ) ^ 2) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hQsqone) hlog2.le
  have hceil :=
    (Nat.ceil_lt_add_one hx0).le
  have hquotlog : 2 * Real.log (Q : ℝ) / Real.log 2 ≤
      2 * Real.log (N + 2 : ℕ) / Real.log 2 :=
    (div_le_div_iff_of_pos_right hlog2).2
      (mul_le_mul_of_nonneg_left hlogQN (by norm_num))
  have hceil' :
      ((Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℕ) : ℝ) ≤
        2 * Real.log (N + 2 : ℕ) / Real.log 2 + 1 := by
    calc
      _ ≤ Real.log ((Q : ℝ) ^ 2) / Real.log 2 + 1 := hceil
      _ = 2 * Real.log (Q : ℝ) / Real.log 2 + 1 := by
        rw [Real.log_pow]
        norm_num
      _ ≤ _ := by linarith
  have hQsqR : ((Q : ℝ) ^ 2) ≤ N := by exact_mod_cast hQsq
  unfold largeSieveBound
  rw [show (1 / (1 / (Q : ℝ) ^ 2)) = (Q : ℝ) ^ 2 by field_simp]
  have hnum :
      2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12 ≤
        (4 / Real.log 2) * Real.log (N + 2 : ℕ) + 14 := by
    calc
      _ ≤ 2 * (2 * Real.log (N + 2 : ℕ) / Real.log 2 + 1) + 12 := by
        nlinarith
      _ = _ := by ring
  rw [div_eq_mul_inv, inv_div, div_one]
  calc
    (↑(N + 2) : ℝ) +
        (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
          (Q : ℝ) ^ 2 ≤
        3 * N +
          ((4 / Real.log 2) * Real.log (N + 2 : ℕ) + 14) * N := by
      apply add_le_add
      · norm_num
        have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      · exact mul_le_mul hnum hQsqR (by positivity) (by positivity)
    _ ≤ (17 + 4 / Real.log 2) * N * Real.log (N + 2 : ℕ) := by
      have hNr : (0 : ℝ) ≤ N := by positivity
      have hc : 0 ≤ 4 / Real.log 2 := by positivity
      nlinarith

namespace LiuWeight

open AnalyticNumberTheory.Sieve

/-- A positive dilation selects distinct coefficients from the original
`[0,N]` energy and therefore cannot increase its square mass. -/
theorem liuPanPrimePowerDilatedCoefficientEnergy_le
    (N e : ℕ) (he : 0 < e) :
    (∑ m ∈ range (N / e + 1),
      ‖(liuPanPrimePowerCoefficient N (e * m) : ℂ)‖ ^ 2) ≤
      ∑ n ∈ range (N + 1), liuPanPrimePowerCoefficient N n ^ 2 := by
  let S := (range (N / e + 1)).image (fun m => e * m)
  calc
    (∑ m ∈ range (N / e + 1),
        ‖(liuPanPrimePowerCoefficient N (e * m) : ℂ)‖ ^ 2) =
        ∑ n ∈ S, liuPanPrimePowerCoefficient N n ^ 2 := by
      rw [Finset.sum_image]
      · apply sum_congr rfl
        intro m hm
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (liuPanPrimePowerCoefficient_nonneg N (e * m))]
      · intro x hx y hy hxy
        exact Nat.mul_left_cancel he hxy
    _ ≤ ∑ n ∈ range (N + 1), liuPanPrimePowerCoefficient N n ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hn' : n ∈ (range (N / e + 1)).image (fun m => e * m) := by
          simpa [S] using hn
        rcases mem_image.mp hn' with ⟨m, hm, rfl⟩
        rw [mem_range] at hm ⊢
        rw [Nat.lt_succ_iff] at hm ⊢
        simpa [mul_comm] using (Nat.le_div_iff_mul_le he).mp hm
      · intro n hn hnS
        exact sq_nonneg _

/-- The maximal primitive mean of every positive dilation is controlled by the
same undilated coefficient energy. -/
theorem liuPanPrimePowerDilatedPrefixMaxMean_le_largeSieve
    (N Q e : ℕ) (hQ : 0 < Q) (he : 0 < e) :
    primitiveCharacterPrefixMaxMean Q
        (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
        (N / e + 1) ≤
      ((1 + Nat.log 2 (N / e + 2) : ℕ) : ℝ) ^ 2 *
        (largeSieveBound (N / e + 2) (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ range (N + 1), liuPanPrimePowerCoefficient N n ^ 2) := by
  refine
    (primitiveCharacterPrefixMaxMean_le_largeSieve_exact Q hQ
      (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
      (N / e + 1)).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply mul_le_mul_of_nonneg_left
      (liuPanPrimePowerDilatedCoefficientEnergy_le N e he)
    exact largeSieveBound_nonneg _ (by positivity)
  · positivity

/-- After taking square roots, every positive dilation has one common
large-sieve and dyadic factor. -/
theorem liuPanPrimePowerDilatedPrefixMaxMean_sqrt_le
    (N Q e : ℕ) (hQ : 0 < Q) (he : 0 < e) :
    Real.sqrt (primitiveCharacterPrefixMaxMean Q
      (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
      (N / e + 1)) ≤
      ((1 + Nat.log 2 (N + 2) : ℕ) : ℝ) *
        Real.sqrt (largeSieveBound (N + 2) (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ range (N + 1), liuPanPrimePowerCoefficient N n ^ 2) := by
  let Le : ℝ := ((1 + Nat.log 2 (N / e + 2) : ℕ) : ℝ)
  let L : ℝ := ((1 + Nat.log 2 (N + 2) : ℕ) : ℝ)
  let E : ℝ :=
    ∑ n ∈ range (N + 1), liuPanPrimePowerCoefficient N n ^ 2
  let Se : ℝ := largeSieveBound (N / e + 2) (1 / (Q : ℝ) ^ 2)
  let S : ℝ := largeSieveBound (N + 2) (1 / (Q : ℝ) ^ 2)
  have hmain := Real.sqrt_le_sqrt
    (liuPanPrimePowerDilatedPrefixMaxMean_le_largeSieve N Q e hQ he)
  have hdiv : N / e ≤ N := Nat.div_le_self N e
  have hLe : Le ≤ L := by
    dsimp [Le, L]
    exact_mod_cast Nat.add_le_add_left
      (Nat.log_mono_right (by omega : N / e + 2 ≤ N + 2)) 1
  have hSE : Se * E ≤ S * E := by
    apply mul_le_mul_of_nonneg_right
    · exact largeSieveBound_mono_length _ _ _ (by omega)
    · dsimp [E]
      positivity
  calc
    Real.sqrt (primitiveCharacterPrefixMaxMean Q
        (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
        (N / e + 1)) ≤ Real.sqrt (Le ^ 2 * (Se * E)) := by
      simpa [Le, Se, E] using hmain
    _ = Le * Real.sqrt (Se * E) := by
      rw [Real.sqrt_mul (sq_nonneg Le), Real.sqrt_sq (by positivity)]
    _ ≤ L * Real.sqrt (S * E) := by
      exact mul_le_mul hLe (Real.sqrt_le_sqrt hSE) (Real.sqrt_nonneg _)
        (by positivity)
    _ = _ := by rfl

/-- The finite set of genuinely nonprincipal characters at a fixed level. -/
noncomputable def liuPanPrimePowerNonprincipalCharacters (q : ℕ) :
    Finset (DirichletCharacter ℂ q) := by
  classical
  exact Finset.univ.erase 1

/-- The primitive-prefix majorant obtained from one induced character after the
exact Möbius dilation expansion. -/
noncomputable def liuPanPrimePowerInducedPrefixUpper
    (N q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ e ∈ (q / χ.conductor).divisors,
    Real.sqrt
      (characterPrefixSquareMax
        (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
        χ.conductor (N / e + 1) χ.primitiveCharacter)

/-- A prefix norm is bounded by the square root of its finite prefix-square
maximum. -/
theorem characterPrefixNorm_le_sqrt_squareMax
    (a : ℕ → ℂ) (q N y : ℕ) (χ : DirichletCharacter ℂ q) (hy : y ≤ N) :
    ‖∑ n ∈ range y, a n * χ (n : ZMod q)‖ ≤
      Real.sqrt (characterPrefixSquareMax a q N χ) := by
  have hsquare :
      characterPrefixSquare a q y χ ≤ characterPrefixSquareMax a q N χ := by
    unfold characterPrefixSquareMax
    have hmem : characterPrefixSquare a q y χ ∈
        (range (N + 1)).image (fun z => characterPrefixSquare a q z χ) :=
      mem_image.mpr
        ⟨y, mem_range.mpr (Nat.lt_succ_iff.mpr hy), rfl⟩
    exact le_max' _ _ hmem
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt hsquare

/-- Every induced-character prefix is bounded linearly by primitive prefixes of
the dilated coefficient sequences. -/
theorem liuPanPrimePowerCharacterPrefixNorm_le_inducedPrefixUpper
    {N y q : ℕ} (hq : 0 < q) (hy : y ≤ N)
    (χ : DirichletCharacter ℂ q) :
    ‖∑ n ∈ range (y + 1),
      (liuPanPrimePowerCoefficient N n : ℂ) * χ (n : ZMod q)‖ ≤
      liuPanPrimePowerInducedPrefixUpper N q χ := by
  let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
  refine
    (characterPrefixSum_norm_le_sum_primitive_dilations
      (fun n => (liuPanPrimePowerCoefficient N n : ℂ)) χ y).trans ?_
  unfold liuPanPrimePowerInducedPrefixUpper
  apply sum_le_sum
  intro e he
  apply characterPrefixNorm_le_sqrt_squareMax
  exact Nat.add_le_add_right (Nat.div_le_div_right hy) 1

/-- Triangle inequality for the exact nonprincipal character expansion, before
any Cauchy--Schwarz step. -/
theorem liuPanPrimePowerNonprincipalDiscrepancy_abs_le_characterPrefixNormSum
    {N y q l : ℕ} (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    |liuPanPrimePowerNonprincipalDiscrepancy N y q l| ≤
      (Nat.totient q : ℝ)⁻¹ *
        ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          ‖∑ n ∈ range (y + 1),
            (liuPanPrimePowerCoefficient N n : ℂ) * χ (n : ZMod q)‖ := by
  classical
  rw [liuPanPrimePowerNonprincipalDiscrepancy_eq_re_nonprincipalCharacterMean
    hq hl]
  calc
    |(liuPanPrimePowerNonprincipalCharacterMean N y q l).re| ≤
        ‖liuPanPrimePowerNonprincipalCharacterMean N y q l‖ :=
      Complex.abs_re_le_norm _
    _ = (Nat.totient q : ℝ)⁻¹ *
        ‖∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          star (χ (l : ZMod q)) *
            ∑ n ∈ range (y + 1),
              (liuPanPrimePowerCoefficient N n : ℂ) * χ (n : ZMod q)‖ := by
      unfold liuPanPrimePowerNonprincipalCharacterMean
        liuPanPrimePowerNonprincipalCharacters
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (Nat.totient q : ℝ)⁻¹ *
        ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          ‖star (χ (l : ZMod q)) *
            ∑ n ∈ range (y + 1),
              (liuPanPrimePowerCoefficient N n : ℂ) * χ (n : ZMod q)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply sum_le_sum
      intro χ hχ
      rw [norm_mul, norm_star]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (dirichletCharacter_norm_le_one q χ (l : ZMod q))

/-- The maximum over residue classes and prefixes is bounded before conductor
regrouping by the linear induced-character primitive-prefix majorant. -/
theorem liuPanPrimePowerNonprincipalDiscrepancyMaxY_le_inducedPrefixUpper
    (N q : ℕ) (hq : 0 < q) :
    liuPanPrimePowerNonprincipalDiscrepancyMaxY N q ≤
      (Nat.totient q : ℝ)⁻¹ *
        ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          liuPanPrimePowerInducedPrefixUpper N q χ := by
  classical
  unfold liuPanPrimePowerNonprincipalDiscrepancyMaxY
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := Nat.le_of_lt_succ (mem_range.mp hy)
  unfold liuPanPrimePowerNonprincipalDiscrepancyMaxL
  dsimp only
  have hS : (unitResidues q).Nonempty := by
    by_cases hq1 : q = 1
    · subst q
      simp
    · have hq2 : 1 < q := by omega
      exact ⟨1, by simp [unitResidues, hq2]⟩
  rw [dif_pos hS]
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨l, hl, rfl⟩
  have hlunit : IsUnit (l : ZMod q) :=
    (ZMod.isUnit_iff_coprime l q).mpr (by
      rw [unitResidues, mem_filter] at hl
      exact hl.2)
  refine
    (liuPanPrimePowerNonprincipalDiscrepancy_abs_le_characterPrefixNormSum
      hq hlunit).trans ?_
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply sum_le_sum
  intro χ hχ
  exact liuPanPrimePowerCharacterPrefixNorm_le_inducedPrefixUpper hq hyN χ

/-- The finite linear transfer that still retains every inducing level and
character.  Its conductor regrouping is an exact finite reindexing. -/
noncomputable def liuPanPrimePowerInducedPrefixTransfer
    (N Q : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 Q,
    liuPanPrimePowerModulusWeight q * (Nat.totient q : ℝ)⁻¹ *
      ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
        liuPanPrimePowerInducedPrefixUpper N q χ

/-- The same finite transfer regrouped first by primitive conductor.  Inducing
levels and their character fibers remain explicit. -/
noncomputable def liuPanPrimePowerConductorPrefixTransfer
    (N Q : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 Q, ∑ q ∈ Icc 1 Q,
    liuPanPrimePowerModulusWeight q * (Nat.totient q : ℝ)⁻¹ *
      ∑ χ ∈ (liuPanPrimePowerNonprincipalCharacters q).filter
          (fun χ => χ.conductor = d),
        liuPanPrimePowerInducedPrefixUpper N q χ

/-- The primitive characters at an exact conductor. -/
noncomputable def liuPanPrimePowerPrimitiveCharacters (d : ℕ) :
    Finset (DirichletCharacter ℂ d) := by
  classical
  exact Finset.univ.filter (fun χ => χ.IsPrimitive)

/-- Primitive characters of conductor `d`, lifted to a fixed multiple `q`. -/
noncomputable def liuPanPrimePowerPrimitiveCharacterLifts
    (q d : ℕ) (hdq : d ∣ q) : Finset (DirichletCharacter ℂ q) := by
  classical
  exact (liuPanPrimePowerPrimitiveCharacters d).image
    (DirichletCharacter.changeLevel hdq)

/-- A primitive character agrees pointwise with its canonical primitive
character.  The pointwise form avoids transporting across conductor equality. -/
theorem primitiveCharacter_apply_eq_self_of_isPrimitive
    {d : ℕ} (ψ : DirichletCharacter ℂ d) (hψ : ψ.IsPrimitive) (a : ℤ) :
    ψ.primitiveCharacter a = ψ a := by
  have hcond : ψ.conductor = d :=
    (DirichletCharacter.isPrimitive_def ψ).mp hψ
  by_cases ha : IsCoprime a (d : ℤ)
  · exact ψ.primitiveCharacter_apply_of_isCoprime ha
  · rw [(DirichletCharacter.apply_eq_zero_iff ψ.primitiveCharacter a).mpr
        (by simpa [hcond] using ha),
      (DirichletCharacter.apply_eq_zero_iff ψ a).mpr ha]

/-- Prefix squares of the primitive character underlying a lifted primitive
character are exactly the original primitive-character prefix squares. -/
theorem characterPrefixSquare_changeLevel_primitive
    {a : ℕ → ℂ} {q d y : ℕ} [NeZero q] (hdq : d ∣ q)
    (ψ : DirichletCharacter ℂ d) (hψ : ψ.IsPrimitive) :
    characterPrefixSquare a (DirichletCharacter.changeLevel hdq ψ).conductor y
        (DirichletCharacter.changeLevel hdq ψ).primitiveCharacter =
      characterPrefixSquare a d y ψ := by
  unfold characterPrefixSquare
  congr 2
  apply sum_congr rfl
  intro n hn
  congr 1
  have h₁ :=
    DirichletCharacter.primitiveCharacter_changeLevel_apply hdq ψ (n : ℤ)
  have h₂ := primitiveCharacter_apply_eq_self_of_isPrimitive ψ hψ (n : ℤ)
  simpa using h₁.trans h₂

/-- The finite prefix-square maximum is unchanged when the character is first
lifted and then canonically reduced to its primitive conductor. -/
theorem characterPrefixSquareMax_changeLevel_primitive
    {a : ℕ → ℂ} {q d M : ℕ} [NeZero q] (hdq : d ∣ q)
    (ψ : DirichletCharacter ℂ d) (hψ : ψ.IsPrimitive) :
    characterPrefixSquareMax a (DirichletCharacter.changeLevel hdq ψ).conductor M
        (DirichletCharacter.changeLevel hdq ψ).primitiveCharacter =
      characterPrefixSquareMax a d M ψ := by
  unfold characterPrefixSquareMax
  have himage :
      (range (M + 1)).image (fun y => characterPrefixSquare a
        (DirichletCharacter.changeLevel hdq ψ).conductor y
        (DirichletCharacter.changeLevel hdq ψ).primitiveCharacter) =
      (range (M + 1)).image (fun y => characterPrefixSquare a d y ψ) := by
    apply image_congr
    intro y hy
    exact characterPrefixSquare_changeLevel_primitive hdq ψ hψ
  apply le_antisymm
  · apply max'_le
    intro z hz
    rw [himage] at hz
    exact le_max' _ _ hz
  · apply max'_le
    intro z hz
    have hz' : z ∈ (range (M + 1)).image (fun y => characterPrefixSquare a
        (DirichletCharacter.changeLevel hdq ψ).conductor y
        (DirichletCharacter.changeLevel hdq ψ).primitiveCharacter) := by
      rw [himage]
      exact hz
    exact le_max' _ _ hz'

/-- Prefix-square maxima are nonnegative. -/
theorem characterPrefixSquareMax_nonneg
    (a : ℕ → ℂ) (q N : ℕ) (χ : DirichletCharacter ℂ q) :
    0 ≤ characterPrefixSquareMax a q N χ := by
  unfold characterPrefixSquareMax
  have hmem := max'_mem
    ((range (N + 1)).image (fun y => characterPrefixSquare a q y χ))
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)
  rcases mem_image.mp hmem with ⟨y, hy, heq⟩
  rw [← heq]
  exact sq_nonneg _

/-- The primitive characters form a subset of all characters, whose cardinality
is Euler's totient. -/
theorem liuPanPrimePowerPrimitiveCharacters_card_le_totient
    (d : ℕ) [NeZero d] :
    (liuPanPrimePowerPrimitiveCharacters d).card ≤ d.totient := by
  calc
    (liuPanPrimePowerPrimitiveCharacters d).card ≤
        (univ : Finset (DirichletCharacter ℂ d)).card := by
      apply card_le_card
      intro ψ hψ
      simp
    _ = Nat.card (DirichletCharacter ℂ d) := by simp
    _ = d.totient :=
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d

/-- Cauchy--Schwarz over the primitive characters at one exact conductor. -/
theorem primitiveCharacterPrefixSqrtSum_le
    (a : ℕ → ℂ) (d M : ℕ) [NeZero d] :
    (∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
      Real.sqrt (characterPrefixSquareMax a d M ψ)) ≤
      Real.sqrt d.totient *
        Real.sqrt (∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
          characterPrefixSquareMax a d M ψ) := by
  let s := liuPanPrimePowerPrimitiveCharacters d
  let X := fun ψ : DirichletCharacter ℂ d =>
    characterPrefixSquareMax a d M ψ
  have hsq : (∑ ψ ∈ s, (Real.sqrt (X ψ)) ^ 2) = ∑ ψ ∈ s, X ψ := by
    apply sum_congr rfl
    intro ψ hψ
    exact Real.sq_sqrt (characterPrefixSquareMax_nonneg a d M ψ)
  calc
    (∑ ψ ∈ s, Real.sqrt (X ψ)) =
        ∑ ψ ∈ s, (1 : ℝ) * Real.sqrt (X ψ) := by simp
    _ ≤ Real.sqrt (∑ ψ ∈ s, (1 : ℝ) ^ 2) *
        Real.sqrt (∑ ψ ∈ s, (Real.sqrt (X ψ)) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s (fun _ => 1)
        (fun ψ => Real.sqrt (X ψ))
    _ = Real.sqrt s.card * Real.sqrt (∑ ψ ∈ s, X ψ) := by
      rw [hsq]
      simp
    _ ≤ Real.sqrt d.totient * Real.sqrt (∑ ψ ∈ s, X ψ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact Real.sqrt_le_sqrt
        (by exact_mod_cast liuPanPrimePowerPrimitiveCharacters_card_le_totient d)

/-- Normalization of every lifted induced upper bound to the original primitive
character and the explicit conductor quotient. -/
theorem liuPanPrimePowerInducedPrefixUpper_changeLevel_primitive
    {N q d : ℕ} [NeZero q] (hdq : d ∣ q)
    (ψ : DirichletCharacter ℂ d) (hψ : ψ.IsPrimitive) :
    liuPanPrimePowerInducedPrefixUpper N q
        (DirichletCharacter.changeLevel hdq ψ) =
      ∑ e ∈ (q / d).divisors,
        Real.sqrt
          (characterPrefixSquareMax
            (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
            d (N / e + 1) ψ) := by
  unfold liuPanPrimePowerInducedPrefixUpper
  have hcond : ψ.conductor = d :=
    (DirichletCharacter.isPrimitive_def ψ).mp hψ
  simp only [DirichletCharacter.conductor_changeLevel, hcond]
  apply sum_congr rfl
  intro e he
  congr 1
  exact characterPrefixSquareMax_changeLevel_primitive hdq ψ hψ

/-- At a fixed positive level and conductor greater than one, the conductor
fiber is exactly the injective image of primitive characters. -/
theorem liuPanPrimePowerNonprincipalCharacters_filter_conductor_eq_lifts
    (q d : ℕ) [NeZero q] (hdq : d ∣ q) (hd : 1 < d) :
    (liuPanPrimePowerNonprincipalCharacters q).filter
        (fun χ => χ.conductor = d) =
      liuPanPrimePowerPrimitiveCharacterLifts q d hdq := by
  classical
  let _ : NeZero d := ⟨by omega⟩
  ext χ
  simp only [liuPanPrimePowerPrimitiveCharacterLifts, mem_filter, mem_image,
    liuPanPrimePowerPrimitiveCharacters, mem_univ, true_and]
  constructor
  · rintro ⟨hχ, hcond⟩
    subst d
    refine ⟨χ.primitiveCharacter,
      χ.primitiveCharacter_isPrimitive, ?_⟩
    simpa using χ.changeLevel_primitiveCharacter
  · rintro ⟨ψ, hprim, rfl⟩
    have hψne : ψ ≠ 1 := by
      intro hψ
      subst ψ
      have hcond := (DirichletCharacter.isPrimitive_def _).mp hprim
      rw [DirichletCharacter.conductor_one] at hcond
      omega
    refine ⟨?_, ?_⟩
    · simpa [liuPanPrimePowerNonprincipalCharacters,
        DirichletCharacter.changeLevel_eq_one_iff hdq] using hψne
    · rw [DirichletCharacter.conductor_changeLevel ψ hdq]
      exact (DirichletCharacter.isPrimitive_def ψ).mp hprim

/-- Reindexing a fixed conductor fiber loses no multiplicity: every induced
character is represented by exactly one primitive character. -/
theorem liuPanPrimePowerInducedPrefixUpper_sum_conductor_eq_primitive_lifts
    (N q d : ℕ) [NeZero q] (hdq : d ∣ q) (hd : 1 < d) :
    (∑ χ ∈ (liuPanPrimePowerNonprincipalCharacters q).filter
        (fun χ => χ.conductor = d),
      liuPanPrimePowerInducedPrefixUpper N q χ) =
      ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
        liuPanPrimePowerInducedPrefixUpper N q
          (DirichletCharacter.changeLevel hdq ψ) := by
  classical
  rw [liuPanPrimePowerNonprincipalCharacters_filter_conductor_eq_lifts
    q d hdq hd]
  unfold liuPanPrimePowerPrimitiveCharacterLifts
  rw [sum_image]
  exact Set.injOn_of_injective
    (DirichletCharacter.changeLevel_injective hdq)

/-- The conductor-first transfer after exact reindexing by primitive
characters.  Divisibility of the conductor into the inducing level and the
conductor-one exclusion remain explicit. -/
noncomputable def liuPanPrimePowerPrimitiveLiftPrefixTransfer
    (N Q : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 Q, ∑ q ∈ Icc 1 Q,
    liuPanPrimePowerModulusWeight q * (Nat.totient q : ℝ)⁻¹ *
      if _hd1 : d = 1 then 0
      else if hdq : d ∣ q then
        ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
          liuPanPrimePowerInducedPrefixUpper N q
            (DirichletCharacter.changeLevel hdq ψ)
      else 0

/-- The primitive-lift transfer after removing all dependent conductor
transports.  Every remaining term is a prefix maximum at the explicit conductor
`d` for a dilated coefficient sequence. -/
noncomputable def liuPanPrimePowerPrimitiveDilationPrefixTransfer
    (N Q : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 Q, ∑ q ∈ Icc 1 Q,
    liuPanPrimePowerModulusWeight q * (Nat.totient q : ℝ)⁻¹ *
      if d = 1 then 0
      else if d ∣ q then
        ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
          ∑ e ∈ (q / d).divisors,
            Real.sqrt
             (characterPrefixSquareMax
               (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
               d (N / e + 1) ψ)
      else 0

/-- Positive multiples of `d` in `[1, Q]` are uniquely parametrized by their
positive cofactors in `[1, Q / d]`. -/
theorem sum_Icc_dvd_eq_sum_Icc_div
    (Q d : ℕ) (hd : 0 < d) (f : ℕ → ℝ) :
    (∑ q ∈ Icc 1 Q, if d ∣ q then f q else 0) =
      ∑ r ∈ Icc 1 (Q / d), f (d * r) := by
  classical
  rw [← sum_filter]
  apply Finset.sum_bij (fun q _ => q / d)
  · intro q hq
    rw [mem_filter, mem_Icc] at hq
    rw [mem_Icc]
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd hq.1.1 hq.2) hd
    · exact Nat.div_le_div_right hq.1.2
  · intro q₁ hq₁ q₂ hq₂ h
    rw [mem_filter] at hq₁ hq₂
    rw [← Nat.mul_div_cancel' hq₁.2, ← Nat.mul_div_cancel' hq₂.2, h]
  · intro r hr
    rw [mem_Icc] at hr
    refine ⟨d * r, ?_, ?_⟩
    · rw [mem_filter, mem_Icc]
      exact ⟨⟨Nat.mul_pos hd hr.1, by
        simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hr.2⟩,
        dvd_mul_right d r⟩
    · exact Nat.mul_div_cancel_left r hd
  · intro q hq
    rw [mem_filter] at hq
    rw [Nat.mul_div_cancel' hq.2]

/-- Summing the complementary cofactor weight over multiples of a fixed
divisor costs at most the finite `H₃` mass. -/
theorem liuPanPrimePowerCofactorWeightSum_le_H3Mass (Q e : ℕ) :
    (∑ r ∈ Icc 1 Q, if e ∣ r then
      liuPanPrimePowerModulusWeight (r / e) /
        Nat.totient (r / e)
    else 0) ≤ liuPanPrimePowerH3Mass Q := by
  by_cases he : e = 0
  · subst e
    simpa using liuPanPrimePowerH3Mass_nonneg Q
  · have hepos : 0 < e := Nat.pos_of_ne_zero he
    rw [sum_Icc_dvd_eq_sum_Icc_div Q e hepos]
    simp only [Nat.mul_div_cancel_left _ hepos]
    unfold liuPanPrimePowerH3Mass
    apply sum_le_sum_of_subset_of_nonneg
    · intro r hr
      rw [mem_Icc] at hr
      rw [mem_range]
      exact Nat.lt_succ_of_le (hr.2.trans (Nat.div_le_self Q e))
    · intro r hr hr'
      exact div_nonneg (liuPanPrimePowerModulusWeight_nonneg r)
        (Nat.cast_nonneg _)

/-- The three-factor decomposition remains an upper bound without a squarefree
hypothesis, because nonsquarefree product weights vanish. -/
theorem liuPanPrimePowerModulusWeight_div_totient_le_three_factors
    {d r e : ℕ} (he : e ∣ r) :
    liuPanPrimePowerModulusWeight (d * r) / Nat.totient (d * r) ≤
      (liuPanPrimePowerModulusWeight d / Nat.totient d) *
        (liuPanPrimePowerModulusWeight e / Nat.totient e) *
          (liuPanPrimePowerModulusWeight (r / e) /
            Nat.totient (r / e)) := by
  by_cases hsq : Squarefree (d * r)
  · exact (liuPanPrimePowerModulusWeight_div_totient_eq_three_factors hsq he).le
  · rw [liuPanPrimePowerModulusWeight_eq_zero_of_not_squarefree hsq]
    simp only [zero_div]
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg (liuPanPrimePowerModulusWeight_nonneg d) (Nat.cast_nonneg _))
        (div_nonneg (liuPanPrimePowerModulusWeight_nonneg e) (Nat.cast_nonneg _)))
      (div_nonneg (liuPanPrimePowerModulusWeight_nonneg (r / e))
        (Nat.cast_nonneg _))

/-- The primitive dilation transfer with inducing levels written uniquely as
`q = d * r`.  This removes the divisibility branch while retaining the
conductor-one exclusion and every cofactor/divisor multiplicity. -/
noncomputable def liuPanPrimePowerCofactorDilationPrefixTransfer
    (N Q : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 Q,
    if d = 1 then 0 else
      ∑ r ∈ Icc 1 (Q / d),
        liuPanPrimePowerModulusWeight (d * r) *
          (Nat.totient (d * r) : ℝ)⁻¹ *
          ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
            ∑ e ∈ r.divisors,
              Real.sqrt
                (characterPrefixSquareMax
                  (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                  d (N / e + 1) ψ)

/-- The conductor/dilation functional left after the complementary cofactor
has been summed under `H₃`. -/
noncomputable def liuPanPrimePowerH3DilationPrefixTransfer
    (N Q : ℕ) : ℝ :=
  liuPanPrimePowerH3Mass Q *
    ∑ d ∈ Icc 2 Q,
      (liuPanPrimePowerModulusWeight d / Nat.totient d) *
        ∑ e ∈ Icc 1 Q,
          (liuPanPrimePowerModulusWeight e / Nat.totient e) *
            ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
              Real.sqrt
                (characterPrefixSquareMax
                  (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                  d (N / e + 1) ψ)

/-- The post-primitive-character Cauchy functional, arranged with the dilation
outside so that the remaining Cauchy--Schwarz inequality is over conductors. -/
noncomputable def liuPanPrimePowerPrimitiveCauchyPrefixTransfer
    (N Q : ℕ) : ℝ :=
  liuPanPrimePowerH3Mass Q *
    ∑ e ∈ Icc 1 Q,
      (liuPanPrimePowerModulusWeight e / Nat.totient e) *
        ∑ d ∈ Icc 2 Q,
          (liuPanPrimePowerModulusWeight d / Nat.totient d) *
            Real.sqrt d.totient *
              Real.sqrt
                (∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
                  characterPrefixSquareMax
                    (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                    d (N / e + 1) ψ)

/-- Algebraic square-root factorization that aligns the conductor coefficient
with `J₉` and the `d / φ(d)` primitive large-sieve weight. -/
theorem liuPanPrimePowerWeight_sqrt_totient_factor
    {d : ℕ} (hd : 0 < d) :
    (liuPanPrimePowerModulusWeight d / Nat.totient d) *
        Real.sqrt d.totient =
      Real.sqrt (liuPanPrimePowerModulusWeight d ^ 2 / d) *
        Real.sqrt ((d : ℝ) / Nat.totient d) := by
  have htot : 0 < (d.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hd
  have hdcast : 0 < (d : ℝ) := by exact_mod_cast hd
  let W : ℝ := liuPanPrimePowerModulusWeight d
  have hW : 0 ≤ W := liuPanPrimePowerModulusWeight_nonneg d
  have hsP : (Real.sqrt (d.totient : ℝ)) ^ 2 = d.totient :=
    Real.sq_sqrt htot.le
  have hsWX :
      (Real.sqrt (W ^ 2 / (d : ℝ))) ^ 2 = W ^ 2 / d :=
    Real.sq_sqrt (div_nonneg (sq_nonneg W) hdcast.le)
  have hsXP :
      (Real.sqrt ((d : ℝ) / d.totient)) ^ 2 = (d : ℝ) / d.totient :=
    Real.sq_sqrt (div_nonneg hdcast.le htot.le)
  have heq :
      (W / (d.totient : ℝ) * Real.sqrt d.totient) ^ 2 =
        (Real.sqrt (W ^ 2 / d) *
          Real.sqrt ((d : ℝ) / d.totient)) ^ 2 := by
    rw [mul_pow, hsP, mul_pow, hsWX, hsXP]
    field_simp
  have hleft : 0 ≤ W / (d.totient : ℝ) * Real.sqrt d.totient :=
    mul_nonneg (div_nonneg hW htot.le) (Real.sqrt_nonneg _)
  have hright :
      0 ≤ Real.sqrt (W ^ 2 / d) * Real.sqrt ((d : ℝ) / d.totient) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

/-- Squaring the squarefree modulus weight gives exactly the `J₉` summand. -/
theorem liuPanPrimePowerModulusWeight_sq_div_eq_J9_term (d : ℕ) :
    liuPanPrimePowerModulusWeight d ^ 2 / d =
      (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
        (9 : ℝ) ^ d.primeFactors.card / d := by
  by_cases hd : Squarefree d
  · have hmu : (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) = 1 := by
      rw [← Int.cast_pow,
        ArithmeticFunction.moebius_sq_eq_one_of_squarefree hd]
      norm_num
    have hp : ((3 : ℝ) ^ d.primeFactors.card) ^ 2 =
        (9 : ℝ) ^ d.primeFactors.card := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    unfold liuPanPrimePowerModulusWeight
    rw [hmu, one_mul, hp]
    simp
  · rw [liuPanPrimePowerModulusWeight_eq_zero_of_not_squarefree hd,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    norm_num

/-- The conductor square mass on `[2,Q]` is contained in the finite `J₉`
mass. -/
theorem liuPanPrimePowerConductorWeightSqSum_le_J9Mass (Q : ℕ) :
    (∑ d ∈ Icc 2 Q, liuPanPrimePowerModulusWeight d ^ 2 / d) ≤
      liuPanPrimePowerJ9Mass Q := by
  simp_rw [liuPanPrimePowerModulusWeight_sq_div_eq_J9_term]
  unfold liuPanPrimePowerJ9Mass
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    rw [mem_Icc] at hd
    rw [mem_range]
    omega
  · intro d hd hd'
    exact div_nonneg
      (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _))
      (Nat.cast_nonneg _)

/-- Restricting the primitive maximal mean to conductors at least two can only
decrease it. -/
theorem primitiveCharacterPrefixMaxMean_Icc_two_le
    (Q : ℕ) (a : ℕ → ℂ) (M : ℕ) :
    (∑ d ∈ Icc 2 Q, ((d : ℝ) / d.totient) *
      ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
        characterPrefixSquareMax a d M ψ) ≤
      primitiveCharacterPrefixMaxMean Q a M := by
  unfold primitiveCharacterPrefixMaxMean
    liuPanPrimePowerPrimitiveCharacters
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    rw [mem_Icc] at hd ⊢
    omega
  · intro d hd hd'
    exact mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (sum_nonneg fun ψ hψ => characterPrefixSquareMax_nonneg a d M ψ)

/-- The exact finite target after both Cauchy--Schwarz steps.  It contains only
the `H₃` and `J₉` masses and the already established primitive maximal mean. -/
noncomputable def liuPanPrimePowerH3J9PrefixTransfer
    (N Q : ℕ) : ℝ :=
  liuPanPrimePowerH3Mass Q *
    ∑ e ∈ Icc 1 Q,
      (liuPanPrimePowerModulusWeight e / Nat.totient e) *
        (Real.sqrt (liuPanPrimePowerJ9Mass Q) *
          Real.sqrt
            (primitiveCharacterPrefixMaxMean Q
              (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
              (N / e + 1)))

/-- The positive dilation weights on `[1,Q]` are contained in `H₃(Q)`. -/
theorem liuPanPrimePowerModulusWeightSum_le_H3Mass (Q : ℕ) :
    (∑ e ∈ Icc 1 Q,
      liuPanPrimePowerModulusWeight e / Nat.totient e) ≤
      liuPanPrimePowerH3Mass Q := by
  unfold liuPanPrimePowerH3Mass
  apply sum_le_sum_of_subset_of_nonneg
  · intro e he
    rw [mem_Icc] at he
    rw [mem_range]
    omega
  · intro e he he'
    exact div_nonneg (liuPanPrimePowerModulusWeight_nonneg e)
      (Nat.cast_nonneg _)

/-- All primitive means in the exact `H₃`/`J₉` transfer are bounded by one
global coefficient energy and one common large-sieve factor. -/
theorem liuPanPrimePowerH3J9PrefixTransfer_le_largeSieve
    (N Q : ℕ) (hQ : 0 < Q) :
    liuPanPrimePowerH3J9PrefixTransfer N Q ≤
      liuPanPrimePowerH3Mass Q ^ 2 *
        Real.sqrt (liuPanPrimePowerJ9Mass Q) *
        (((1 + Nat.log 2 (N + 2) : ℕ) : ℝ) *
          Real.sqrt (largeSieveBound (N + 2) (1 / (Q : ℝ) ^ 2) *
            ∑ n ∈ range (N + 1),
              liuPanPrimePowerCoefficient N n ^ 2)) := by
  let C : ℝ :=
    Real.sqrt (liuPanPrimePowerJ9Mass Q) *
      (((1 + Nat.log 2 (N + 2) : ℕ) : ℝ) *
        Real.sqrt (largeSieveBound (N + 2) (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ range (N + 1),
            liuPanPrimePowerCoefficient N n ^ 2))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hinner :
      (∑ e ∈ Icc 1 Q,
        (liuPanPrimePowerModulusWeight e / Nat.totient e) *
          (Real.sqrt (liuPanPrimePowerJ9Mass Q) *
            Real.sqrt
              (primitiveCharacterPrefixMaxMean Q
                (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                (N / e + 1)))) ≤ liuPanPrimePowerH3Mass Q * C := by
    calc
      _ ≤ ∑ e ∈ Icc 1 Q,
          (liuPanPrimePowerModulusWeight e / Nat.totient e) * C := by
        apply sum_le_sum
        intro e he
        apply mul_le_mul_of_nonneg_left
        · dsimp only [C]
          apply mul_le_mul_of_nonneg_left
          · exact liuPanPrimePowerDilatedPrefixMaxMean_sqrt_le N Q e hQ
              (mem_Icc.mp he).1
          · exact Real.sqrt_nonneg _
        · exact div_nonneg (liuPanPrimePowerModulusWeight_nonneg e)
            (Nat.cast_nonneg _)
      _ = (∑ e ∈ Icc 1 Q,
          liuPanPrimePowerModulusWeight e / Nat.totient e) * C := by
        rw [sum_mul]
      _ ≤ liuPanPrimePowerH3Mass Q * C :=
        mul_le_mul_of_nonneg_right
          (liuPanPrimePowerModulusWeightSum_le_H3Mass Q) hC
  unfold liuPanPrimePowerH3J9PrefixTransfer
  calc
    liuPanPrimePowerH3Mass Q * _ ≤
        liuPanPrimePowerH3Mass Q * (liuPanPrimePowerH3Mass Q * C) :=
      mul_le_mul_of_nonneg_left hinner
        (liuPanPrimePowerH3Mass_nonneg Q)
    _ = _ := by
      dsimp [C]
      ring

/-- Abstract cofactor summation: after the squarefree three-factor estimate,
the complementary quotient is absorbed by `H₃`. -/
theorem liuPanPrimePowerCofactorSum_le_H3Mass
    (Q d : ℕ) (F : ℕ → ℝ) (hF : ∀ e, 0 ≤ F e) :
    (∑ r ∈ Icc 1 (Q / d),
      (liuPanPrimePowerModulusWeight (d * r) /
        Nat.totient (d * r)) *
        ∑ e ∈ r.divisors, F e) ≤
      liuPanPrimePowerH3Mass Q *
        (liuPanPrimePowerModulusWeight d / Nat.totient d) *
          ∑ e ∈ Icc 1 Q,
            (liuPanPrimePowerModulusWeight e / Nat.totient e) * F e := by
  let A : ℕ → ℝ := fun n =>
    liuPanPrimePowerModulusWeight n / Nat.totient n
  have hA : ∀ n, 0 ≤ A n := fun n =>
    div_nonneg (liuPanPrimePowerModulusWeight_nonneg n) (Nat.cast_nonneg _)
  calc
    (∑ r ∈ Icc 1 (Q / d), A (d * r) * ∑ e ∈ r.divisors, F e) ≤
        ∑ r ∈ Icc 1 (Q / d),
          ∑ e ∈ r.divisors, (A d * A e * A (r / e)) * F e := by
      apply sum_le_sum
      intro r hr
      rw [mul_sum]
      apply sum_le_sum
      intro e he
      apply mul_le_mul_of_nonneg_right _ (hF e)
      exact liuPanPrimePowerModulusWeight_div_totient_le_three_factors
        (Nat.dvd_of_mem_divisors he)
    _ ≤ ∑ r ∈ Icc 1 (Q / d),
        ∑ e ∈ Icc 1 Q,
          if e ∣ r then (A d * A e * A (r / e)) * F e else 0 := by
      apply sum_le_sum
      intro r hr
      rw [← sum_filter]
      apply sum_le_sum_of_subset_of_nonneg
      · intro e he
        rw [mem_filter, mem_Icc]
        have her : e ∣ r := Nat.dvd_of_mem_divisors he
        refine ⟨?_, her⟩
        constructor
        · exact Nat.pos_of_dvd_of_pos her (mem_Icc.mp hr).1
        · exact (Nat.le_of_dvd (mem_Icc.mp hr).1 her).trans
            ((mem_Icc.mp hr).2.trans (Nat.div_le_self Q d))
      · intro e he he'
        exact mul_nonneg (mul_nonneg (mul_nonneg (hA d) (hA e))
          (hA (r / e))) (hF e)
    _ ≤ ∑ r ∈ Icc 1 Q,
        ∑ e ∈ Icc 1 Q,
          if e ∣ r then (A d * A e * A (r / e)) * F e else 0 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro r hr
        rw [mem_Icc] at hr ⊢
        exact ⟨hr.1, hr.2.trans (Nat.div_le_self Q d)⟩
      · intro r hr hr'
        apply sum_nonneg
        intro e he
        split
        · exact mul_nonneg (mul_nonneg (mul_nonneg (hA d) (hA e))
            (hA (r / e))) (hF e)
        · exact le_rfl
    _ = ∑ e ∈ Icc 1 Q,
        (A d * A e * F e) *
          ∑ r ∈ Icc 1 Q, if e ∣ r then A (r / e) else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro e he
      rw [mul_sum]
      apply sum_congr rfl
      intro r hr
      split <;> ring
    _ ≤ ∑ e ∈ Icc 1 Q,
        (A d * A e * F e) * liuPanPrimePowerH3Mass Q := by
      apply sum_le_sum
      intro e he
      apply mul_le_mul_of_nonneg_left
        (liuPanPrimePowerCofactorWeightSum_le_H3Mass Q e)
      exact mul_nonneg (mul_nonneg (hA d) (hA e)) (hF e)
    _ = liuPanPrimePowerH3Mass Q * A d *
        ∑ e ∈ Icc 1 Q, A e * F e := by
      rw [mul_sum]
      apply sum_congr rfl
      intro e he
      ring

/-- The exact cofactor transfer is bounded by the explicit post-`H₃`
conductor/dilation functional. -/
theorem liuPanPrimePowerCofactorDilationPrefixTransfer_le_H3
    (N Q : ℕ) :
    liuPanPrimePowerCofactorDilationPrefixTransfer N Q ≤
      liuPanPrimePowerH3DilationPrefixTransfer N Q := by
  classical
  unfold liuPanPrimePowerCofactorDilationPrefixTransfer
    liuPanPrimePowerH3DilationPrefixTransfer
  let G : ℕ → ℝ := fun d =>
    ∑ r ∈ Icc 1 (Q / d),
      liuPanPrimePowerModulusWeight (d * r) *
        (Nat.totient (d * r) : ℝ)⁻¹ *
        ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
          ∑ e ∈ r.divisors,
            Real.sqrt
              (characterPrefixSquareMax
                (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                d (N / e + 1) ψ)
  change (∑ d ∈ Icc 1 Q, if d = 1 then 0 else G d) ≤ _
  have hsum :
      (∑ d ∈ Icc 1 Q, if d = 1 then 0 else G d) =
        ∑ d ∈ (Icc 1 Q).filter (fun d => d ≠ 1), G d := by
    rw [sum_filter]
    apply sum_congr rfl
    intro d hd
    by_cases hd1 : d = 1 <;> simp [hd1]
  have hfilter :
      (Icc 1 Q).filter (fun d => d ≠ 1) = Icc 2 Q := by
    ext d
    simp only [mem_filter, mem_Icc]
    omega
  rw [hsum, hfilter, mul_sum]
  apply sum_le_sum
  intro d hd
  dsimp only [G]
  let F : ℕ → ℝ := fun e =>
    ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
      Real.sqrt
        (characterPrefixSquareMax
          (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
          d (N / e + 1) ψ)
  have hF : ∀ e, 0 ≤ F e := fun e =>
    sum_nonneg fun ψ hψ => Real.sqrt_nonneg _
  calc
    (∑ r ∈ Icc 1 (Q / d),
        liuPanPrimePowerModulusWeight (d * r) *
          (Nat.totient (d * r) : ℝ)⁻¹ *
          ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
            ∑ e ∈ r.divisors,
              Real.sqrt
                (characterPrefixSquareMax
                  (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                  d (N / e + 1) ψ)) =
        ∑ r ∈ Icc 1 (Q / d),
          (liuPanPrimePowerModulusWeight (d * r) /
            Nat.totient (d * r)) *
            ∑ e ∈ r.divisors, F e := by
      apply sum_congr rfl
      intro r hr
      rw [show liuPanPrimePowerModulusWeight (d * r) *
          (Nat.totient (d * r) : ℝ)⁻¹ =
          liuPanPrimePowerModulusWeight (d * r) /
            Nat.totient (d * r) by
        simp [div_eq_mul_inv]]
      congr 1
      simp only [F]
      rw [sum_comm]
    _ ≤ liuPanPrimePowerH3Mass Q *
        (liuPanPrimePowerModulusWeight d / Nat.totient d) *
          ∑ e ∈ Icc 1 Q,
            (liuPanPrimePowerModulusWeight e / Nat.totient e) * F e :=
      liuPanPrimePowerCofactorSum_le_H3Mass Q d F hF
    _ = liuPanPrimePowerH3Mass Q *
        ((liuPanPrimePowerModulusWeight d / Nat.totient d) *
          ∑ e ∈ Icc 1 Q,
            (liuPanPrimePowerModulusWeight e / Nat.totient e) *
              ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
                Real.sqrt
                  (characterPrefixSquareMax
                    (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                    d (N / e + 1) ψ)) := by
      simp only [F]
      ring

/-- Cauchy--Schwarz over the primitive characters at each exact conductor,
without summing over inducing levels first. -/
theorem liuPanPrimePowerH3DilationPrefixTransfer_le_primitiveCauchy
    (N Q : ℕ) :
    liuPanPrimePowerH3DilationPrefixTransfer N Q ≤
      liuPanPrimePowerPrimitiveCauchyPrefixTransfer N Q := by
  classical
  unfold liuPanPrimePowerH3DilationPrefixTransfer
    liuPanPrimePowerPrimitiveCauchyPrefixTransfer
  apply mul_le_mul_of_nonneg_left _ (liuPanPrimePowerH3Mass_nonneg Q)
  calc
    (∑ d ∈ Icc 2 Q,
        (liuPanPrimePowerModulusWeight d / Nat.totient d) *
          ∑ e ∈ Icc 1 Q,
            (liuPanPrimePowerModulusWeight e / Nat.totient e) *
              ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
                Real.sqrt
                  (characterPrefixSquareMax
                    (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                    d (N / e + 1) ψ)) =
        ∑ d ∈ Icc 2 Q, ∑ e ∈ Icc 1 Q,
          (liuPanPrimePowerModulusWeight e / Nat.totient e) *
            ((liuPanPrimePowerModulusWeight d / Nat.totient d) *
              ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
                Real.sqrt
                  (characterPrefixSquareMax
                    (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                    d (N / e + 1) ψ)) := by
      apply sum_congr rfl
      intro d hd
      rw [mul_sum]
      apply sum_congr rfl
      intro e he
      ring
    _ = ∑ e ∈ Icc 1 Q, ∑ d ∈ Icc 2 Q,
          (liuPanPrimePowerModulusWeight e / Nat.totient e) *
            ((liuPanPrimePowerModulusWeight d / Nat.totient d) *
              ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
                Real.sqrt
                  (characterPrefixSquareMax
                    (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                    d (N / e + 1) ψ)) := by
      rw [sum_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro e he
      rw [mul_sum]
      apply sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left
      · have hdpos : 0 < d :=
          lt_of_lt_of_le (by norm_num) (mem_Icc.mp hd).1
        let _ : NeZero d := ⟨Nat.ne_of_gt hdpos⟩
        calc
          (liuPanPrimePowerModulusWeight d / Nat.totient d) *
              ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
                Real.sqrt
                  (characterPrefixSquareMax
                    (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                    d (N / e + 1) ψ) ≤
              (liuPanPrimePowerModulusWeight d / Nat.totient d) *
                (Real.sqrt d.totient *
                  Real.sqrt
                    (∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
                      characterPrefixSquareMax
                        (fun m =>
                          (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                        d (N / e + 1) ψ)) := by
            apply mul_le_mul_of_nonneg_left
              (primitiveCharacterPrefixSqrtSum_le
                (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                d (N / e + 1))
            exact div_nonneg (liuPanPrimePowerModulusWeight_nonneg d)
              (Nat.cast_nonneg _)
          _ = _ := by ring
      · exact div_nonneg (liuPanPrimePowerModulusWeight_nonneg e)
          (Nat.cast_nonneg _)

/-- Cauchy--Schwarz over conductors gives the exact finite `H₃`/`J₉`
primitive-maximal functional. -/
theorem liuPanPrimePowerPrimitiveCauchyPrefixTransfer_le_H3_J9
    (N Q : ℕ) :
    liuPanPrimePowerPrimitiveCauchyPrefixTransfer N Q ≤
      liuPanPrimePowerH3J9PrefixTransfer N Q := by
  classical
  unfold liuPanPrimePowerPrimitiveCauchyPrefixTransfer
    liuPanPrimePowerH3J9PrefixTransfer
  apply mul_le_mul_of_nonneg_left _ (liuPanPrimePowerH3Mass_nonneg Q)
  apply sum_le_sum
  intro e he
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg (liuPanPrimePowerModulusWeight_nonneg e) (Nat.cast_nonneg _))
  let a : ℕ → ℂ := fun m =>
    (liuPanPrimePowerCoefficient N (e * m) : ℂ)
  let P : ℕ → ℝ := fun d =>
    ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
      characterPrefixSquareMax a d (N / e + 1) ψ
  let f : ℕ → ℝ := fun d =>
    Real.sqrt (liuPanPrimePowerModulusWeight d ^ 2 / d)
  let g : ℕ → ℝ := fun d =>
    Real.sqrt (((d : ℝ) / d.totient) * P d)
  calc
    (∑ d ∈ Icc 2 Q,
        (liuPanPrimePowerModulusWeight d / Nat.totient d) *
          Real.sqrt d.totient * Real.sqrt (P d)) =
        ∑ d ∈ Icc 2 Q, f d * g d := by
      apply sum_congr rfl
      intro d hd
      have hdpos : 0 < d :=
        lt_of_lt_of_le (by norm_num) (mem_Icc.mp hd).1
      rw [liuPanPrimePowerWeight_sqrt_totient_factor hdpos]
      dsimp only [f, g]
      rw [Real.sqrt_mul (div_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg _))]
      ring
    _ ≤ Real.sqrt (∑ d ∈ Icc 2 Q, f d ^ 2) *
        Real.sqrt (∑ d ∈ Icc 2 Q, g d ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt (Icc 2 Q) f g
    _ = Real.sqrt
          (∑ d ∈ Icc 2 Q,
            liuPanPrimePowerModulusWeight d ^ 2 / d) *
        Real.sqrt
          (∑ d ∈ Icc 2 Q, ((d : ℝ) / d.totient) * P d) := by
      congr 1
      · congr 1
        apply sum_congr rfl
        intro d hd
        exact Real.sq_sqrt
          (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      · congr 1
        apply sum_congr rfl
        intro d hd
        exact Real.sq_sqrt
          (mul_nonneg
            (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            (sum_nonneg fun ψ hψ =>
              characterPrefixSquareMax_nonneg a d (N / e + 1) ψ))
    _ ≤ Real.sqrt (liuPanPrimePowerJ9Mass Q) *
        Real.sqrt (primitiveCharacterPrefixMaxMean Q a (N / e + 1)) := by
      apply mul_le_mul
      · exact Real.sqrt_le_sqrt
          (liuPanPrimePowerConductorWeightSqSum_le_J9Mass Q)
      · exact Real.sqrt_le_sqrt
          (primitiveCharacterPrefixMaxMean_Icc_two_le Q a (N / e + 1))
      · exact Real.sqrt_nonneg _
      · exact Real.sqrt_nonneg _

/-- Exact conductor/cofactor reindexing of the primitive dilation transfer. -/
theorem liuPanPrimePowerPrimitiveDilationPrefixTransfer_eq_cofactor
    (N Q : ℕ) :
    liuPanPrimePowerPrimitiveDilationPrefixTransfer N Q =
      liuPanPrimePowerCofactorDilationPrefixTransfer N Q := by
  classical
  unfold liuPanPrimePowerPrimitiveDilationPrefixTransfer
    liuPanPrimePowerCofactorDilationPrefixTransfer
  apply sum_congr rfl
  intro d hdmem
  by_cases hd1 : d = 1
  · simp [hd1]
  · rw [if_neg hd1]
    have hdpos : 0 < d := (mem_Icc.mp hdmem).1
    let F : ℕ → ℝ := fun q =>
      liuPanPrimePowerModulusWeight q * (Nat.totient q : ℝ)⁻¹ *
        ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
          ∑ e ∈ (q / d).divisors,
            Real.sqrt
              (characterPrefixSquareMax
                (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                d (N / e + 1) ψ)
    calc
      (∑ q ∈ Icc 1 Q,
        liuPanPrimePowerModulusWeight q * (Nat.totient q : ℝ)⁻¹ *
          if d = 1 then 0
          else if d ∣ q then
            ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
              ∑ e ∈ (q / d).divisors,
                Real.sqrt
                  (characterPrefixSquareMax
                    (fun m => (liuPanPrimePowerCoefficient N (e * m) : ℂ))
                    d (N / e + 1) ψ)
          else 0) =
          ∑ q ∈ Icc 1 Q, if d ∣ q then F q else 0 := by
        apply sum_congr rfl
        intro q hq
        simp only [hd1, if_false]
        by_cases hdq : d ∣ q
        · simp [hdq, F]
        · simp [hdq]
      _ = ∑ r ∈ Icc 1 (Q / d), F (d * r) :=
        sum_Icc_dvd_eq_sum_Icc_div Q d hdpos F
      _ = _ := by
        apply sum_congr rfl
        intro r hr
        simp only [F, Nat.mul_div_cancel_left r hdpos]

/-- Full exact finite reduction of the primitive dilation transfer to the
`H₃`/`J₉` masses and primitive maximal large-sieve means. -/
theorem liuPanPrimePowerPrimitiveDilationPrefixTransfer_le_H3_J9
    (N Q : ℕ) :
    liuPanPrimePowerPrimitiveDilationPrefixTransfer N Q ≤
      liuPanPrimePowerH3J9PrefixTransfer N Q := by
  calc
    liuPanPrimePowerPrimitiveDilationPrefixTransfer N Q =
        liuPanPrimePowerCofactorDilationPrefixTransfer N Q :=
      liuPanPrimePowerPrimitiveDilationPrefixTransfer_eq_cofactor N Q
    _ ≤ liuPanPrimePowerH3DilationPrefixTransfer N Q :=
      liuPanPrimePowerCofactorDilationPrefixTransfer_le_H3 N Q
    _ ≤ liuPanPrimePowerPrimitiveCauchyPrefixTransfer N Q :=
      liuPanPrimePowerH3DilationPrefixTransfer_le_primitiveCauchy N Q
    _ ≤ liuPanPrimePowerH3J9PrefixTransfer N Q :=
      liuPanPrimePowerPrimitiveCauchyPrefixTransfer_le_H3_J9 N Q

/-- Exact normalization of the conductor-first lift transfer. -/
theorem liuPanPrimePowerPrimitiveLiftPrefixTransfer_eq_dilation
    (N Q : ℕ) :
    liuPanPrimePowerPrimitiveLiftPrefixTransfer N Q =
      liuPanPrimePowerPrimitiveDilationPrefixTransfer N Q := by
  classical
  unfold liuPanPrimePowerPrimitiveLiftPrefixTransfer
    liuPanPrimePowerPrimitiveDilationPrefixTransfer
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro q hq
  congr 1
  by_cases hd1 : d = 1
  · simp [hd1]
  · simp only [dif_neg hd1, if_neg hd1]
    by_cases hdq : d ∣ q
    · simp only [dif_pos hdq, if_pos hdq]
      have hqpos : 0 < q := (mem_Icc.mp hq).1
      let _ : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
      apply sum_congr rfl
      intro ψ hψ
      rw [liuPanPrimePowerInducedPrefixUpper_changeLevel_primitive hdq ψ]
      simpa [liuPanPrimePowerPrimitiveCharacters] using hψ
    · simp [hdq]

/-- The conductor-one fiber is absent from every positive-level nonprincipal
character set. -/
theorem liuPanPrimePowerNonprincipalCharacters_filter_conductor_one
    (q : ℕ) [NeZero q] :
    (liuPanPrimePowerNonprincipalCharacters q).filter
        (fun χ => χ.conductor = 1) = ∅ := by
  classical
  rw [Finset.filter_eq_empty_iff]
  intro χ hχ hcond
  have hχne : χ ≠ 1 := by
    simpa [liuPanPrimePowerNonprincipalCharacters] using hχ
  exact hχne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hcond)

/-- Exact primitive-character reindexing of the whole conductor transfer.  No
character or inducing-level multiplicity is discarded. -/
theorem liuPanPrimePowerConductorPrefixTransfer_eq_primitiveLiftPrefixTransfer
    (N Q : ℕ) :
    liuPanPrimePowerConductorPrefixTransfer N Q =
      liuPanPrimePowerPrimitiveLiftPrefixTransfer N Q := by
  classical
  unfold liuPanPrimePowerConductorPrefixTransfer
    liuPanPrimePowerPrimitiveLiftPrefixTransfer
  apply sum_congr rfl
  intro d hdmem
  apply sum_congr rfl
  intro q hqmem
  have hqpos : 0 < q := (mem_Icc.mp hqmem).1
  let _ : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  congr 1
  by_cases hd1 : d = 1
  · subst d
    rw [liuPanPrimePowerNonprincipalCharacters_filter_conductor_one q]
    simp
  · have hd : 1 < d := by
      have := (mem_Icc.mp hdmem).1
      omega
    by_cases hdq : d ∣ q
    · rw [dif_neg hd1, dif_pos hdq]
      exact liuPanPrimePowerInducedPrefixUpper_sum_conductor_eq_primitive_lifts
        N q d hdq hd
    · have hempty :
          (liuPanPrimePowerNonprincipalCharacters q).filter
              (fun χ => χ.conductor = d) = ∅ := by
        rw [filter_eq_empty_iff]
        intro χ hχ hcond
        exact hdq (hcond ▸ χ.conductor_dvd_level)
      rw [hempty, dif_neg hd1, dif_neg hdq]
      simp

/-- Exact finite conductor regrouping, with no character multiplicity or
coprimality factor suppressed. -/
theorem liuPanPrimePowerInducedPrefixTransfer_eq_conductorPrefixTransfer
    (N Q : ℕ) :
    liuPanPrimePowerInducedPrefixTransfer N Q =
      liuPanPrimePowerConductorPrefixTransfer N Q := by
  classical
  unfold liuPanPrimePowerInducedPrefixTransfer
    liuPanPrimePowerConductorPrefixTransfer
  have hfiber : ∀ q ∈ Icc 1 Q,
      (∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
        liuPanPrimePowerInducedPrefixUpper N q χ) =
        ∑ d ∈ Icc 1 Q,
          ∑ χ ∈ (liuPanPrimePowerNonprincipalCharacters q).filter
              (fun χ => χ.conductor = d),
            liuPanPrimePowerInducedPrefixUpper N q χ := by
    intro q hq
    have hqpos : 0 < q := (mem_Icc.mp hq).1
    let _ : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
    calc
      (∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          liuPanPrimePowerInducedPrefixUpper N q χ) =
          ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
            ∑ d ∈ Icc 1 Q,
              if χ.conductor = d then
                liuPanPrimePowerInducedPrefixUpper N q χ else 0 := by
        apply sum_congr rfl
        intro χ hχ
        have hdpos : 0 < χ.conductor :=
          Nat.pos_of_ne_zero χ.conductor_ne_zero
        have hdQ : χ.conductor ≤ Q :=
          (Nat.le_of_dvd hqpos χ.conductor_dvd_level).trans
            (mem_Icc.mp hq).2
        have hdmem : χ.conductor ∈ Icc 1 Q :=
          mem_Icc.mpr ⟨hdpos, hdQ⟩
        simp [hdmem]
      _ = ∑ d ∈ Icc 1 Q,
          ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
            if χ.conductor = d then
              liuPanPrimePowerInducedPrefixUpper N q χ else 0 := by
        rw [sum_comm]
      _ = _ := by
        apply sum_congr rfl
        intro d hd
        rw [sum_filter]
  calc
    (∑ q ∈ Icc 1 Q,
      liuPanPrimePowerModulusWeight q * (Nat.totient q : ℝ)⁻¹ *
        ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          liuPanPrimePowerInducedPrefixUpper N q χ) =
        ∑ q ∈ Icc 1 Q,
          liuPanPrimePowerModulusWeight q * (Nat.totient q : ℝ)⁻¹ *
            ∑ d ∈ Icc 1 Q,
              ∑ χ ∈ (liuPanPrimePowerNonprincipalCharacters q).filter
                  (fun χ => χ.conductor = d),
                liuPanPrimePowerInducedPrefixUpper N q χ := by
      apply sum_congr rfl
      intro q hq
      rw [hfiber q hq]
    _ = ∑ q ∈ Icc 1 Q, ∑ d ∈ Icc 1 Q,
        liuPanPrimePowerModulusWeight q * (Nat.totient q : ℝ)⁻¹ *
          ∑ χ ∈ (liuPanPrimePowerNonprincipalCharacters q).filter
              (fun χ => χ.conductor = d),
            liuPanPrimePowerInducedPrefixUpper N q χ := by
      simp_rw [Finset.mul_sum]
    _ = _ := by rw [sum_comm]

/-- The original residual is bounded by the finite induced-character transfer.
The modulus-zero term is annihilated by its weight; modulus one contributes no
nonprincipal character. -/
theorem liuMainPanPrimePowerCharacterNoncoprimeResidual_le_inducedPrefixTransfer
    (N : ℕ) (B : ℝ) :
    liuMainPanPrimePowerCharacterNoncoprimeResidual N B ≤
      liuPanPrimePowerInducedPrefixTransfer N (panModulusCutoff N B) := by
  classical
  let Q := panModulusCutoff N B
  have hrange : range (Q + 1) = insert 0 (Icc 1 Q) := by
    ext q
    simp
    omega
  unfold liuMainPanPrimePowerCharacterNoncoprimeResidual
    liuPanPrimePowerInducedPrefixTransfer
  change
    (∑ q ∈ range (Q + 1),
      liuPanPrimePowerModulusWeight q *
        liuPanPrimePowerNonprincipalDiscrepancyMaxY N q) ≤ _
  rw [hrange]
  rw [sum_insert (by simp : 0 ∉ Icc 1 Q)]
  simp only [liuPanPrimePowerModulusWeight_zero, zero_mul, zero_add]
  apply sum_le_sum
  intro q hq
  have hqpos : 0 < q := (mem_Icc.mp hq).1
  calc
    liuPanPrimePowerModulusWeight q *
        liuPanPrimePowerNonprincipalDiscrepancyMaxY N q ≤
      liuPanPrimePowerModulusWeight q *
        ((Nat.totient q : ℝ)⁻¹ *
          ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
            liuPanPrimePowerInducedPrefixUpper N q χ) :=
      mul_le_mul_of_nonneg_left
        (liuPanPrimePowerNonprincipalDiscrepancyMaxY_le_inducedPrefixUpper
          N q hqpos)
        (liuPanPrimePowerModulusWeight_nonneg q)
    _ = liuPanPrimePowerModulusWeight q * (Nat.totient q : ℝ)⁻¹ *
        ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          liuPanPrimePowerInducedPrefixUpper N q χ := by ring

/-- Conductor-first form of the exact residual transfer. -/
theorem liuMainPanPrimePowerCharacterNoncoprimeResidual_le_conductorPrefixTransfer
    (N : ℕ) (B : ℝ) :
    liuMainPanPrimePowerCharacterNoncoprimeResidual N B ≤
      liuPanPrimePowerConductorPrefixTransfer N (panModulusCutoff N B) := by
  rw [← liuPanPrimePowerInducedPrefixTransfer_eq_conductorPrefixTransfer]
  exact
    liuMainPanPrimePowerCharacterNoncoprimeResidual_le_inducedPrefixTransfer N B

/-- The original residual transferred all the way to uniquely indexed primitive
characters, while retaining every inducing level and Möbius dilation. -/
theorem liuMainPanPrimePowerCharacterNoncoprimeResidual_le_primitiveLiftPrefixTransfer
    (N : ℕ) (B : ℝ) :
    liuMainPanPrimePowerCharacterNoncoprimeResidual N B ≤
      liuPanPrimePowerPrimitiveLiftPrefixTransfer N
        (panModulusCutoff N B) := by
  calc
    liuMainPanPrimePowerCharacterNoncoprimeResidual N B ≤
        liuPanPrimePowerConductorPrefixTransfer N
          (panModulusCutoff N B) :=
      liuMainPanPrimePowerCharacterNoncoprimeResidual_le_conductorPrefixTransfer
        N B
    _ = liuPanPrimePowerPrimitiveLiftPrefixTransfer N
        (panModulusCutoff N B) :=
      liuPanPrimePowerConductorPrefixTransfer_eq_primitiveLiftPrefixTransfer
        N (panModulusCutoff N B)

/-- Exact finite `H₃`/`J₉` maximal large-sieve reduction for the original
nonprincipal prime-power residual. -/
theorem liuMainPanPrimePowerCharacterNoncoprimeResidual_le_H3_J9
    (N : ℕ) (B : ℝ) :
    liuMainPanPrimePowerCharacterNoncoprimeResidual N B ≤
      liuPanPrimePowerH3J9PrefixTransfer N (panModulusCutoff N B) := by
  calc
    liuMainPanPrimePowerCharacterNoncoprimeResidual N B ≤
        liuPanPrimePowerPrimitiveLiftPrefixTransfer N
          (panModulusCutoff N B) :=
      liuMainPanPrimePowerCharacterNoncoprimeResidual_le_primitiveLiftPrefixTransfer
        N B
    _ = liuPanPrimePowerPrimitiveDilationPrefixTransfer N
          (panModulusCutoff N B) :=
      liuPanPrimePowerPrimitiveLiftPrefixTransfer_eq_dilation N
        (panModulusCutoff N B)
    _ ≤ liuPanPrimePowerH3J9PrefixTransfer N
          (panModulusCutoff N B) :=
      liuPanPrimePowerPrimitiveDilationPrefixTransfer_le_H3_J9 N
        (panModulusCutoff N B)

/-- A zero conductor cutoff leaves only modulus zero, whose Möbius weight
annihilates the residual. -/
theorem liuMainPanPrimePowerCharacterNoncoprimeResidual_eq_zero_of_cutoff_eq_zero
    (N : ℕ) (B : ℝ) (hQ : panModulusCutoff N B = 0) :
    liuMainPanPrimePowerCharacterNoncoprimeResidual N B = 0 := by
  simp [liuMainPanPrimePowerCharacterNoncoprimeResidual, hQ,
    liuPanPrimePowerModulusWeight_zero]

/-- The original residual is bounded by one explicit maximal large-sieve factor
and the global square mass of the collected source coefficient. -/
theorem liuMainPanPrimePowerCharacterNoncoprimeResidual_le_largeSieveEnergy
    (N : ℕ) (B : ℝ) (hQ : 0 < panModulusCutoff N B) :
    liuMainPanPrimePowerCharacterNoncoprimeResidual N B ≤
      liuPanPrimePowerH3Mass (panModulusCutoff N B) ^ 2 *
        Real.sqrt (liuPanPrimePowerJ9Mass (panModulusCutoff N B)) *
        (((1 + Nat.log 2 (N + 2) : ℕ) : ℝ) *
          Real.sqrt
            (largeSieveBound (N + 2)
                (1 / (panModulusCutoff N B : ℝ) ^ 2) *
              ∑ n ∈ range (N + 1),
                liuPanPrimePowerCoefficient N n ^ 2)) := by
  exact (liuMainPanPrimePowerCharacterNoncoprimeResidual_le_H3_J9 N B).trans
    (liuPanPrimePowerH3J9PrefixTransfer_le_largeSieve N
      (panModulusCutoff N B) hQ)

/-- Substituting the source coefficient's `L²` estimate leaves only explicit
scalar factors in the residual bound. -/
theorem
    liuMainPanPrimePowerCharacterNoncoprimeResidual_le_largeSieveCoefficientBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (B : ℝ), 8 ≤ N →
      0 < panModulusCutoff N B →
      liuMainPanPrimePowerCharacterNoncoprimeResidual N B ≤
        liuPanPrimePowerH3Mass (panModulusCutoff N B) ^ 2 *
          Real.sqrt (liuPanPrimePowerJ9Mass (panModulusCutoff N B)) *
          (((1 + Nat.log 2 (N + 2) : ℕ) : ℝ) *
            Real.sqrt
              (largeSieveBound (N + 2)
                  (1 / (panModulusCutoff N B : ℝ) ^ 2) *
                ((1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
                  (C * (N : ℝ) ^ (107 / 120 : ℝ))))) := by
  obtain ⟨C, hC, htotal⟩ := liuPanPrimePowerTotal_le_rpow
  refine ⟨C, hC, ?_⟩
  intro N B hN hQ
  refine
    (liuMainPanPrimePowerCharacterNoncoprimeResidual_le_largeSieveEnergy
      N B hQ).trans ?_
  have hroot :
      Real.sqrt
          (largeSieveBound (N + 2)
              (1 / (panModulusCutoff N B : ℝ) ^ 2) *
            ∑ n ∈ range (N + 1),
              liuPanPrimePowerCoefficient N n ^ 2) ≤
        Real.sqrt
          (largeSieveBound (N + 2)
              (1 / (panModulusCutoff N B : ℝ) ^ 2) *
            ((1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
              (C * (N : ℝ) ^ (107 / 120 : ℝ)))) := by
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left
    · exact (liuPanPrimePowerCoefficient_sq_sum_le N).trans
        (mul_le_mul_of_nonneg_left (htotal N hN) (by positivity))
    · exact largeSieveBound_nonneg _ (by positivity)
  let F :=
    liuPanPrimePowerH3Mass (panModulusCutoff N B) ^ 2 *
      Real.sqrt (liuPanPrimePowerJ9Mass (panModulusCutoff N B)) *
      ((1 + Nat.log 2 (N + 2) : ℕ) : ℝ)
  calc
    _ = F * Real.sqrt
          (largeSieveBound (N + 2)
              (1 / (panModulusCutoff N B : ℝ) ^ 2) *
            ∑ n ∈ range (N + 1),
              liuPanPrimePowerCoefficient N n ^ 2) := by
        dsimp [F]
        ring
    _ ≤ F * Real.sqrt
          (largeSieveBound (N + 2)
              (1 / (panModulusCutoff N B : ℝ) ^ 2) *
            ((1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
              (C * (N : ℝ) ^ (107 / 120 : ℝ)))) :=
      mul_le_mul_of_nonneg_left hroot (by
        dsimp [F]
        positivity)
    _ = _ := by
      dsimp [F]
      ring

/-- For nonnegative logarithmic cutoff exponent, the Pan conductor range lies
inside the square-root range. -/
theorem panModulusCutoff_sq_le
    (N : ℕ) (B : ℝ) (hN : 3 ≤ N) (hB : 0 ≤ B) :
    panModulusCutoff N B ^ 2 ≤ N := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hlog : (1 : ℝ) ≤ Real.log N := by
    apply (Real.le_log_iff_exp_le hNpos).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hden : 1 ≤ Real.log N ^ B := Real.one_le_rpow hlog hB
  have hquot : (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B ≤
      (N : ℝ) ^ (1 / 2 : ℝ) :=
    div_le_self (Real.rpow_nonneg hNpos.le _) hden
  have hcut : (panModulusCutoff N B : ℝ) ≤
      (N : ℝ) ^ (1 / 2 : ℝ) :=
    (Nat.floor_le (by positivity)).trans hquot
  have hsqR : (panModulusCutoff N B : ℝ) ^ 2 ≤ (N : ℝ) := by
    calc
      (panModulusCutoff N B : ℝ) ^ 2 ≤
          ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcut 2
      _ = (N : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        norm_num
  exact_mod_cast hsqR

private theorem liuPanPrimePower_log_add_two_le_two_mul_log
    (N : ℕ) (hN : 3 ≤ N) :
    Real.log (N + 2 : ℕ) ≤ 2 * Real.log N := by
  have hmul : N + 2 ≤ N * N := by nlinarith
  calc
    Real.log (N + 2 : ℕ) ≤ Real.log (N * N : ℕ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hmul)
    _ = 2 * Real.log N := by
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      ring

theorem liuPanPrimePower_cutoff_log_add_two_le_two_mul_log
    (N : ℕ) (B : ℝ) (hN : 3 ≤ N) (hB : 0 ≤ B) :
    Real.log (panModulusCutoff N B + 2 : ℕ) ≤ 2 * Real.log N := by
  have hQsq := panModulusCutoff_sq_le N B hN hB
  have hQle : panModulusCutoff N B ≤ N := by
    by_cases hQ : panModulusCutoff N B = 0
    · simp [hQ]
    · calc
        panModulusCutoff N B ≤
            panModulusCutoff N B * panModulusCutoff N B :=
          le_mul_of_one_le_right' (Nat.one_le_iff_ne_zero.mpr hQ)
        _ = panModulusCutoff N B ^ 2 := by ring
        _ ≤ N := hQsq
  exact (Real.log_le_log (by positivity)
    (by exact_mod_cast (show panModulusCutoff N B + 2 ≤ N + 2 by omega))).trans
      (liuPanPrimePower_log_add_two_le_two_mul_log N hN)

/-- The weak large-sieve constant is now fully eliminated from the residual
bound at Pan's cutoff.  Only the explicit `H₃`, `J₉`, and logarithmic scalar
factors remain. -/
theorem
    liuMainPanPrimePowerCharacterNoncoprimeResidual_le_explicitScalar :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (B : ℝ), 8 ≤ N → 0 ≤ B →
      0 < panModulusCutoff N B →
      liuMainPanPrimePowerCharacterNoncoprimeResidual N B ≤
        liuPanPrimePowerH3Mass (panModulusCutoff N B) ^ 2 *
          Real.sqrt (liuPanPrimePowerJ9Mass (panModulusCutoff N B)) *
          (((1 + Nat.log 2 (N + 2) : ℕ) : ℝ) *
            Real.sqrt
              (((17 + 4 / Real.log 2) * N * Real.log (N + 2 : ℕ)) *
                ((1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
                  (C * (N : ℝ) ^ (107 / 120 : ℝ))))) := by
  obtain ⟨C, hC, hbound⟩ :=
    liuMainPanPrimePowerCharacterNoncoprimeResidual_le_largeSieveCoefficientBound
  refine ⟨C, hC, ?_⟩
  intro N B hN hB hQ
  refine (hbound N B hN hQ).trans ?_
  have hls :
      largeSieveBound (N + 2)
          (1 / (panModulusCutoff N B : ℝ) ^ 2) ≤
        (17 + 4 / Real.log 2) * N * Real.log (N + 2 : ℕ) :=
    largeSieveBound_le_mul_log_of_sq_le N (panModulusCutoff N B)
      (by omega) hQ (panModulusCutoff_sq_le N B (by omega) hB)
  have hfactor :
      0 ≤ (1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
        (C * (N : ℝ) ^ (107 / 120 : ℝ)) := by positivity
  have hroot := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_right hls hfactor)
  let F :=
    liuPanPrimePowerH3Mass (panModulusCutoff N B) ^ 2 *
      Real.sqrt (liuPanPrimePowerJ9Mass (panModulusCutoff N B)) *
      ((1 + Nat.log 2 (N + 2) : ℕ) : ℝ)
  calc
    _ = F * Real.sqrt
          (largeSieveBound (N + 2)
              (1 / (panModulusCutoff N B : ℝ) ^ 2) *
            ((1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
              (C * (N : ℝ) ^ (107 / 120 : ℝ)))) := by
        dsimp [F]
        ring
    _ ≤ F * Real.sqrt
          (((17 + 4 / Real.log 2) * N * Real.log (N + 2 : ℕ)) *
            ((1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
              (C * (N : ℝ) ^ (107 / 120 : ℝ)))) :=
      mul_le_mul_of_nonneg_left hroot (by
        dsimp [F]
        positivity)
    _ = _ := by
      dsimp [F]
      ring

/-- The maximal nonprincipal residual has the source exponent `227/240`; all
conductor, dyadic, and coefficient-multiplicity costs fit in `log(N)^20`. -/
theorem
    liuMainPanPrimePowerCharacterNoncoprimeResidual_le_rpow_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (B : ℝ), 8 ≤ N → 0 ≤ B →
      liuMainPanPrimePowerCharacterNoncoprimeResidual N B ≤
        C * (N : ℝ) ^ (227 / 240 : ℝ) * Real.log N ^ (20 : ℝ) := by
  obtain ⟨C₀, hC₀, hscalar⟩ :=
    liuMainPanPrimePowerCharacterNoncoprimeResidual_le_explicitScalar
  obtain ⟨C₃, hC₃, hH₃⟩ := liuPanPrimePowerH3Mass_le_polylog
  obtain ⟨C₉, hC₉, hJ₉⟩ := liuPanPrimePowerJ9Mass_le_polylog
  let D₃ : ℝ := 64 * C₃
  let D₉ : ℝ := 512 * C₉
  let DL : ℝ := 1 + 2 / Real.log 2
  let DR : ℝ :=
    2 * (17 + 4 / Real.log 2) * (1 + 4 / Real.log 2 ^ 2) * C₀
  let C : ℝ := D₃ ^ 2 * Real.sqrt D₉ * DL * Real.sqrt DR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD₃ : 0 < D₃ := by positivity
  have hD₉ : 0 < D₉ := by positivity
  have hDL : 0 < DL := by positivity
  have hDR : 0 < DR := by
    dsimp [DR]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N B hN hB
  by_cases hQ : panModulusCutoff N B = 0
  · rw [liuMainPanPrimePowerCharacterNoncoprimeResidual_eq_zero_of_cutoff_eq_zero
      N B hQ]
    positivity
  have hQpos : 0 < panModulusCutoff N B := Nat.pos_of_ne_zero hQ
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  have hL : (1 : ℝ) ≤ Real.log N := by
    apply (Real.le_log_iff_exp_le hNpos).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ N by omega))
  have hlogQ :
      Real.log (panModulusCutoff N B + 2 : ℕ) ≤ 2 * Real.log N :=
    liuPanPrimePower_cutoff_log_add_two_le_two_mul_log N B (by omega) hB
  have hlogN2 : Real.log (N + 2 : ℕ) ≤ 2 * Real.log N :=
    liuPanPrimePower_log_add_two_le_two_mul_log N (by omega)
  have hlogN1 : Real.log (N + 1 : ℕ) ≤ 2 * Real.log N := by
    exact (Real.log_le_log (by positivity)
      (by exact_mod_cast (show N + 1 ≤ N + 2 by omega))).trans hlogN2
  have hH :
      liuPanPrimePowerH3Mass (panModulusCutoff N B) ≤
        D₃ * Real.log N ^ (6 : ℕ) := by
    calc
      liuPanPrimePowerH3Mass (panModulusCutoff N B) ≤
          C₃ * Real.log (panModulusCutoff N B + 2 : ℕ) ^ (6 : ℕ) :=
        by simpa only [Nat.cast_add, Nat.cast_ofNat, Real.rpow_ofNat] using
          hH₃ (panModulusCutoff N B)
      _ ≤ C₃ * (2 * Real.log N) ^ (6 : ℕ) := by
        gcongr
      _ = D₃ * Real.log N ^ (6 : ℕ) := by
        dsimp [D₃]
        ring
  have hJ :
      liuPanPrimePowerJ9Mass (panModulusCutoff N B) ≤
        D₉ * Real.log N ^ (9 : ℕ) := by
    calc
      liuPanPrimePowerJ9Mass (panModulusCutoff N B) ≤
          C₉ * Real.log (panModulusCutoff N B + 2 : ℕ) ^ (9 : ℕ) :=
        by simpa only [Nat.cast_add, Nat.cast_ofNat, Real.rpow_ofNat] using
          hJ₉ (panModulusCutoff N B)
      _ ≤ C₉ * (2 * Real.log N) ^ (9 : ℕ) := by
        gcongr
      _ = D₉ * Real.log N ^ (9 : ℕ) := by
        dsimp [D₉]
        ring
  have hrootJ :
      Real.sqrt (liuPanPrimePowerJ9Mass (panModulusCutoff N B)) ≤
        Real.sqrt D₉ * Real.log N ^ 5 := by
    rw [Real.sqrt_le_left (by positivity)]
    calc
      liuPanPrimePowerJ9Mass (panModulusCutoff N B) ≤
          D₉ * Real.log N ^ 9 := hJ
      _ ≤ D₉ * Real.log N ^ 10 := by
        gcongr
        norm_num
      _ = (Real.sqrt D₉ * Real.log N ^ 5) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hD₉.le]
        ring
  have hnatlog :
      ((Nat.log 2 (N + 2) : ℕ) : ℝ) ≤
        2 * Real.log N / Real.log 2 := by
    calc
      ((Nat.log 2 (N + 2) : ℕ) : ℝ) ≤
          Real.log (N + 2 : ℕ) / Real.log 2 := by
        simpa [Real.log_div_log] using Real.natLog_le_logb (N + 2) 2
      _ ≤ 2 * Real.log N / Real.log 2 :=
        div_le_div_of_nonneg_right hlogN2 hlog2.le
  have hdyadic :
      ((1 + Nat.log 2 (N + 2) : ℕ) : ℝ) ≤ DL * Real.log N := by
    calc
      ((1 + Nat.log 2 (N + 2) : ℕ) : ℝ) =
          1 + ((Nat.log 2 (N + 2) : ℕ) : ℝ) := by norm_num
      _ ≤ 1 + 2 * Real.log N / Real.log 2 := by gcongr
      _ ≤ DL * Real.log N := by
        dsimp [DL]
        field_simp
        nlinarith
  have hratio :
      1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2 ≤
        (1 + 4 / Real.log 2 ^ 2) * Real.log N ^ 2 := by
    have hsquare :
        (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2 ≤
          (2 * Real.log N / Real.log 2) ^ 2 := by
      gcongr
    calc
      1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2 ≤
          1 + (2 * Real.log N / Real.log 2) ^ 2 := by gcongr
      _ ≤ (1 + 4 / Real.log 2 ^ 2) * Real.log N ^ 2 := by
        have hLsq : (1 : ℝ) ≤ Real.log N ^ 2 := by
          exact one_le_pow₀ hL
        field_simp
        nlinarith
  have hinner :
      ((17 + 4 / Real.log 2) * N * Real.log (N + 2 : ℕ)) *
          ((1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
            (C₀ * (N : ℝ) ^ (107 / 120 : ℝ))) ≤
        DR * (N : ℝ) ^ (227 / 120 : ℝ) * Real.log N ^ 3 := by
    have hNmul :
        (N : ℝ) * (N : ℝ) ^ (107 / 120 : ℝ) =
          (N : ℝ) ^ (227 / 120 : ℝ) := by
      calc
        (N : ℝ) * (N : ℝ) ^ (107 / 120 : ℝ) =
            (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (107 / 120 : ℝ) := by
          rw [Real.rpow_one]
        _ = (N : ℝ) ^ ((1 : ℝ) + 107 / 120) := by
          rw [Real.rpow_add hNpos]
        _ = (N : ℝ) ^ (227 / 120 : ℝ) := by norm_num
    calc
      ((17 + 4 / Real.log 2) * N * Real.log (N + 2 : ℕ)) *
          ((1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
            (C₀ * (N : ℝ) ^ (107 / 120 : ℝ))) ≤
          ((17 + 4 / Real.log 2) * N * (2 * Real.log N)) *
            (((1 + 4 / Real.log 2 ^ 2) * Real.log N ^ 2) *
              (C₀ * (N : ℝ) ^ (107 / 120 : ℝ))) := by
        gcongr
      _ = DR * (N : ℝ) ^ (227 / 120 : ℝ) * Real.log N ^ 3 := by
        dsimp [DR]
        rw [← hNmul]
        ring
  have hrootInner :
      Real.sqrt
          (((17 + 4 / Real.log 2) * N * Real.log (N + 2 : ℕ)) *
            ((1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
              (C₀ * (N : ℝ) ^ (107 / 120 : ℝ)))) ≤
        Real.sqrt DR * (N : ℝ) ^ (227 / 240 : ℝ) *
          Real.log N ^ 2 := by
    have hNpowSquare :
        ((N : ℝ) ^ (227 / 240 : ℝ)) ^ 2 =
          (N : ℝ) ^ (227 / 120 : ℝ) := by
      rw [pow_two, ← Real.rpow_add hNpos]
      norm_num
    rw [Real.sqrt_le_left (by positivity)]
    calc
      ((17 + 4 / Real.log 2) * N * Real.log (N + 2 : ℕ)) *
          ((1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
            (C₀ * (N : ℝ) ^ (107 / 120 : ℝ))) ≤
          DR * (N : ℝ) ^ (227 / 120 : ℝ) * Real.log N ^ 3 := hinner
      _ ≤ DR * (N : ℝ) ^ (227 / 120 : ℝ) * Real.log N ^ 4 := by
        gcongr
        norm_num
      _ = (Real.sqrt DR * (N : ℝ) ^ (227 / 240 : ℝ) *
          Real.log N ^ 2) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hDR.le, hNpowSquare]
        ring
  calc
    liuMainPanPrimePowerCharacterNoncoprimeResidual N B ≤
        liuPanPrimePowerH3Mass (panModulusCutoff N B) ^ 2 *
          Real.sqrt (liuPanPrimePowerJ9Mass (panModulusCutoff N B)) *
          (((1 + Nat.log 2 (N + 2) : ℕ) : ℝ) *
            Real.sqrt
              (((17 + 4 / Real.log 2) * N * Real.log (N + 2 : ℕ)) *
                ((1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
                  (C₀ * (N : ℝ) ^ (107 / 120 : ℝ))))) :=
      hscalar N B hN hB hQpos
    _ ≤ (D₃ * Real.log N ^ 6) ^ 2 *
          (Real.sqrt D₉ * Real.log N ^ 5) *
          ((DL * Real.log N) *
            (Real.sqrt DR * (N : ℝ) ^ (227 / 240 : ℝ) *
              Real.log N ^ 2)) := by
      gcongr
      exact liuPanPrimePowerH3Mass_nonneg _
    _ = C * (N : ℝ) ^ (227 / 240 : ℝ) *
          Real.log N ^ (20 : ℝ) := by
      rw [Real.rpow_ofNat]
      dsimp [C]
      ring

end LiuWeight

end MathlibNt.SieveTheory
