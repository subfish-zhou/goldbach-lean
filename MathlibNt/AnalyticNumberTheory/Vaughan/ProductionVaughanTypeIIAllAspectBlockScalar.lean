import MathlibNt.AnalyticNumberTheory.Vaughan.ProductionVaughanTypeIIAspectSafeBlockL1
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveWeightedFamilyMassBound
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# All-aspect scalar payment for actual Vaughan Type-II cells

This checker leaf starts from the honest explicit collected-shell estimate at
`Q = 2i`, applies the exact `1/i` cell normalization, and expands the literal
weak `largeSieveBound`.  No aspect split or complementary analytic source is
used.  The sharp family-mass term is paid in full.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section
set_option maxHeartbeats 1600000

private lemma allAspect_log_ge_two (N : ℕ) (hN : 9 ≤ N) :
    2 ≤ Real.log (4 * N + 4 : ℕ) := by
  have harg : (16 : ℝ) ≤ (4 * N + 4 : ℕ) := by
    exact_mod_cast (show 16 ≤ 4 * N + 4 by omega)
  have hlog : Real.log (16 : ℝ) ≤ Real.log (4 * N + 4 : ℕ) :=
    Real.log_le_log (by norm_num) harg
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [hlog16] at hlog
  nlinarith [Real.log_two_gt_d9]

private lemma allAspect_qFactor_le
    (N i : ℕ) (hN : 9 ≤ N) (hi : 0 < i) (h2i : 2 * i ≤ N) :
    primitiveBilinearQFactor (2 * i) ≤ 15 * Real.log (4 * N + 4 : ℕ) := by
  let L := Real.log (4 * N + 4 : ℕ)
  have hQ : 0 < 2 * i := Nat.mul_pos (by omega) hi
  have hQ1 : 1 ≤ 2 * i := hQ
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpow : Real.log (((2 * i : ℕ) : ℝ) ^ 2) =
      2 * Real.log ((2 * i : ℕ) : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogpow0 : 0 ≤ Real.log (((2 * i : ℕ) : ℝ) ^ 2) := by
    rw [hlogpow]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hQ1))
  have harg0 : 0 ≤ Real.log (((2 * i : ℕ) : ℝ) ^ 2) / Real.log 2 :=
    div_nonneg hlogpow0 hlog2pos.le
  have hceil := (Nat.ceil_lt_add_one harg0).le
  have hratio : Real.log (((2 * i : ℕ) : ℝ) ^ 2) / Real.log 2 ≤
      2 * Real.log (((2 * i : ℕ) : ℝ) ^ 2) := by
    apply (div_le_iff₀ hlog2pos).2
    nlinarith
  have hlogQL : Real.log ((2 * i : ℕ) : ℝ) ≤ L := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (h2i.trans (show N ≤ 4 * N + 4 by omega))
  have hlogpowL : Real.log (((2 * i : ℕ) : ℝ) ^ 2) ≤ 2 * L := by
    rw [hlogpow]
    linarith
  have hceilL :
      (Nat.ceil (Real.log (((2 * i : ℕ) : ℝ) ^ 2) / Real.log 2) : ℝ) ≤
        4 * L + 1 := hceil.trans (by linarith)
  have hL2 : 2 ≤ L := allAspect_log_ge_two N hN
  unfold primitiveBilinearQFactor
  linarith

private lemma allAspect_active_geometry
    (N u v k l : ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    1 ≤ vaughanTypeIIRectangularX N k ∧
    vaughanTypeIIRectangularT N k l ≤ vaughanTypeIIRectangularX N k ∧
    vaughanTypeIIRectangularD k * vaughanTypeIIRectangularX N k ≤ N := by
  have hcorner := (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).2
  have hl : 2 ^ l ≤ N / 2 ^ k :=
    (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).2
      (by simpa [mul_comm] using hcorner)
  constructor
  · simpa [vaughanTypeIIRectangularX] using
      (show 1 ≤ N / 2 ^ k from
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))).trans hl)
  constructor
  · unfold vaughanTypeIIRectangularT vaughanTypeIIRectangularX
    have hlone : 1 ≤ 2 ^ l :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    omega
  · simpa [vaughanTypeIIRectangularD, vaughanTypeIIRectangularX] using
      Nat.mul_div_le N (2 ^ k)

private lemma allAspect_shell_lower_bounds
    (N u v k l : ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    u + 1 ≤ 2 * vaughanTypeIIRectangularD k ∧
    v + 1 ≤ 2 * 2 ^ l := by
  have hrect := (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).1
  rw [vaughanCanonicalDyadicRectangles, Finset.mem_product] at hrect
  have hk := hrect.1
  have hl := hrect.2
  rw [mem_vaughanCanonicalDyadicBases_iff] at hk hl
  obtain ⟨d, hd, -⟩ := hk
  obtain ⟨e, he, -⟩ := hl
  have hdmem := mem_vaughanCanonicalDyadicBlock.mp hd
  have hemel := mem_vaughanCanonicalDyadicBlock.mp he
  have hdpow := (vaughanCanonicalDyadicBlock_pow_bounds hd).2
  have hepow := (vaughanCanonicalDyadicBlock_pow_bounds he).2
  constructor
  · unfold vaughanTypeIIRectangularD
    rw [pow_succ] at hdpow
    have hu' : u + 1 ≤ d := by omega
    exact hu'.trans (by simpa [mul_comm] using hdpow.le)
  · rw [pow_succ] at hepow
    have hv' : v + 1 ≤ e := by omega
    exact hv'.trans (by simpa [mul_comm] using hepow.le)

private lemma allAspect_smoothing_le (N : ℕ) (hN : 9 ≤ N) :
    1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi ≤
      8 * Real.log (4 * N + 4 : ℕ) := by
  let L := Real.log (4 * N + 4 : ℕ)
  have hL2 : 2 ≤ L := allAspect_log_ge_two N hN
  have hlog0 : 0 ≤ Real.log ((2 * N : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * N by omega))
  have hlogL : Real.log ((2 * N : ℕ) : ℝ) ≤ L := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show 2 * N ≤ 4 * N + 4 by omega)
  have hdiv : (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi ≤
      (14 * L + 4) / 3 := by
    apply (div_le_iff₀ Real.pi_pos).2
    have hnum : 0 ≤ 14 * L + 4 := by positivity
    nlinarith [Real.pi_gt_three]
  linarith

/-- Exact expansion of the two literal weak large-sieve factors.  The right
length `T` and both physical dimensions `D,X` remain visible. -/
theorem vaughanTypeIIRectangularRexp_le_expanded_allAspect
    (N Q u v k l : ℕ) (hQ : 0 < Q)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanTypeIIRectangularRexp N k l Q ≤
      Real.sqrt (27 * Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5) *
        ((vaughanTypeIIRectangularD k : ℝ) * vaughanTypeIIRectangularX N k +
          primitiveBilinearQFactor Q * Q *
            ((vaughanTypeIIRectangularD k : ℝ) *
                Real.sqrt (vaughanTypeIIRectangularX N k) +
              (vaughanTypeIIRectangularX N k : ℝ) *
                Real.sqrt (vaughanTypeIIRectangularD k)) +
          primitiveBilinearQFactor Q ^ 2 * (Q : ℝ) ^ 2 *
            Real.sqrt (vaughanTypeIIRectangularD k) *
            Real.sqrt (vaughanTypeIIRectangularX N k)) := by
  let d : ℝ := vaughanTypeIIRectangularD k
  let x : ℝ := vaughanTypeIIRectangularX N k
  let t : ℝ := vaughanTypeIIRectangularT N k l
  let q : ℝ := Q
  let c : ℝ := primitiveBilinearQFactor Q
  let z : ℝ := Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5
  let rd := Real.sqrt d
  let rx := Real.sqrt x
  have hd : 0 ≤ d := by positivity
  have hx : 0 ≤ x := by positivity
  have ht : 0 ≤ t := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hc : 1 ≤ c := by simpa [c] using one_le_primitiveBilinearQFactor Q
  have hc0 : 0 ≤ c := by linarith
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have htx : t ≤ x := by
    dsimp [t, x]
    exact_mod_cast (allAspect_active_geometry N u v k l hactive).2.1
  have hrd : 0 ≤ rd := Real.sqrt_nonneg _
  have hrx : 0 ≤ rx := Real.sqrt_nonneg _
  have hrd2 : rd ^ 2 = d := Real.sq_sqrt hd
  have hrx2 : rx ^ 2 = x := Real.sq_sqrt hx
  have hLSD : largeSieveBound (vaughanTypeIIRectangularD k)
      (1 / (Q : ℝ) ^ 2) = d + c * q ^ 2 := by
    simpa only [vaughanBilinearLargeSieveConstant, d, q, c,
      primitiveBilinearQFactor] using
      vaughanBilinearLargeSieveConstant_eq_explicit
        (vaughanTypeIIRectangularD k) Q hQ
  have hLST : largeSieveBound (vaughanTypeIIRectangularT N k l)
      (1 / (Q : ℝ) ^ 2) = t + c * q ^ 2 := by
    simpa only [vaughanBilinearLargeSieveConstant, t, q, c,
      primitiveBilinearQFactor] using
      vaughanBilinearLargeSieveConstant_eq_explicit
        (vaughanTypeIIRectangularT N k l) Q hQ
  let B : ℝ := d * x + c * q * (d * rx + x * rd) + c ^ 2 * q ^ 2 * rd * rx
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hdmaj : d + c * q ^ 2 ≤ (rd + c * q) ^ 2 := by
    rw [show d = rd ^ 2 by rw [hrd2]]
    nlinarith [mul_nonneg hc0 hq0, sq_nonneg (c - 1)]
  have hxmaj : x + c * q ^ 2 ≤ (rx + c * q) ^ 2 := by
    rw [show x = rx ^ 2 by rw [hrx2]]
    nlinarith [mul_nonneg hc0 hq0, sq_nonneg (c - 1)]
  have hcore : d * x * (d + c * q ^ 2) * (t + c * q ^ 2) ≤ B ^ 2 := by
    have htmaj : t + c * q ^ 2 ≤ x + c * q ^ 2 := add_le_add htx le_rfl
    calc
      _ ≤ d * x * (d + c * q ^ 2) * (x + c * q ^ 2) := by gcongr
      _ ≤ d * x * (rd + c * q) ^ 2 * (rx + c * q) ^ 2 := by gcongr
      _ = B ^ 2 := by dsimp [B]; rw [← hrd2, ← hrx2]; ring
  have hrad1 : 0 ≤ (d + c * q ^ 2) * d := by positivity
  have hrad2 : 0 ≤ (t + c * q ^ 2) * (27 * x * z) := by positivity
  have hradZ : 0 ≤ 27 * z := by positivity
  unfold vaughanTypeIIRectangularRexp vaughanTypeIIRectangularEright at ⊢
  rw [hLSD, hLST]
  change Real.sqrt ((d + c * q ^ 2) * d) *
      Real.sqrt ((t + c * q ^ 2) * (27 * x * z)) ≤ Real.sqrt (27 * z) * B
  have hlhs : 0 ≤ Real.sqrt ((d + c * q ^ 2) * d) *
      Real.sqrt ((t + c * q ^ 2) * (27 * x * z)) := by positivity
  have hrhs : 0 ≤ Real.sqrt (27 * z) * B := by positivity
  have hsq :
      (Real.sqrt ((d + c * q ^ 2) * d) *
        Real.sqrt ((t + c * q ^ 2) * (27 * x * z))) ^ 2 ≤
      (Real.sqrt (27 * z) * B) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad1, Real.sq_sqrt hrad2,
      mul_pow, Real.sq_sqrt hradZ]
    calc
      _ = 27 * z * (d * x * (d + c * q ^ 2) * (t + c * q ^ 2)) := by ring
      _ ≤ 27 * z * B ^ 2 := mul_le_mul_of_nonneg_left hcore (by positivity)
  exact le_of_sq_le_sq hsq hrhs

private lemma allAspect_root_log_le
    (N u v k l : ℕ) (hN : 9 ≤ N)
    (_hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    Real.sqrt (27 * Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5) ≤
      6 * Real.log (4 * N + 4 : ℕ) ^ 3 := by
  let L := Real.log (4 * N + 4 : ℕ)
  let LX := Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ)
  have hLX0 : 0 ≤ LX := by
    exact Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ vaughanTypeIIRectangularX N k + 1 by omega))
  have hXL : vaughanTypeIIRectangularX N k + 1 ≤ 4 * N + 4 := by
    calc
      vaughanTypeIIRectangularX N k + 1 ≤ N + 1 :=
        Nat.add_le_add_right (by
          unfold vaughanTypeIIRectangularX
          exact Nat.div_le_self N (2 ^ k)) 1
      _ ≤ 4 * N + 4 := by omega
  have hLXL : LX ≤ L := Real.log_le_log (by positivity) (by exact_mod_cast hXL)
  have hL2 : 2 ≤ L := allAspect_log_ge_two N hN
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      27 * LX ^ 5 ≤ 27 * L ^ 5 := by gcongr
      _ ≤ (6 * L ^ 3) ^ 2 := by
        have hL0 : 0 ≤ L := by linarith
        nlinarith [mul_nonneg (pow_nonneg hL0 5) (sub_nonneg.mpr hL2)]

private lemma allAspect_L1exp_le
    (N u v k l : ℕ) (hN : 9 ≤ N)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanTypeIIRectangularL1exp N k l ≤
      8 * (N : ℝ) * Real.log (4 * N + 4 : ℕ) ^ 3 := by
  let L := Real.log (4 * N + 4 : ℕ)
  let X := vaughanTypeIIRectangularX N k
  let D := vaughanTypeIIRectangularD k
  let T := vaughanTypeIIRectangularT N k l
  have hg := allAspect_active_geometry N u v k l hactive
  have hTX : (T : ℝ) ≤ X := by exact_mod_cast hg.2.1
  have hDX : (D : ℝ) * X ≤ N := by exact_mod_cast hg.2.2
  have hlog0 : 0 ≤ Real.log (X + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X + 1 by omega))
  have hlogL : Real.log (X + 1 : ℕ) ≤ L := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show X + 1 ≤ 4 * N + 4 by
      calc
        X + 1 ≤ N + 1 := Nat.add_le_add_right (by
          dsimp [X]
          unfold vaughanTypeIIRectangularX
          exact Nat.div_le_self N (2 ^ k)) 1
        _ ≤ 4 * N + 4 := by omega)
  have hL2 : 2 ≤ L := allAspect_log_ge_two N hN
  have hsqrtD : Real.sqrt ((D : ℝ) * D) = D := by
    rw [show (D : ℝ) * D = (D : ℝ) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  unfold vaughanTypeIIRectangularL1exp vaughanTypeIIRectangularEright
  change Real.sqrt ((D : ℝ) * D) *
      Real.sqrt ((T : ℝ) * (27 * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 5)) ≤ _
  rw [hsqrtD]
  have hroot : Real.sqrt ((T : ℝ) *
      (27 * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 5)) ≤ 8 * X * L ^ 3 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · calc
        _ ≤ (X : ℝ) * (27 * X * L ^ 5) := by gcongr
        _ ≤ (8 * X * L ^ 3) ^ 2 := by
          have hL0 : 0 ≤ L := by linarith
          nlinarith [mul_nonneg (sq_nonneg (X : ℝ)) (pow_nonneg hL0 5)]
  calc
    _ ≤ D * (8 * X * L ^ 3) := mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (8 * L ^ 3) * (D * X) := by ring
    _ ≤ (8 * L ^ 3) * N := mul_le_mul_of_nonneg_left hDX (by positivity)
    _ = _ := by ring

private lemma allAspect_sharpTerm_le
    (N Q C u v k l i : ℕ) (G : ProductionConductorBlockGeometry N Q C)
    (hN : 9 ≤ N) (hi : 0 < i)
    (hcell : G.cell i ⊆ Finset.Ioc i (2 * i))
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    (1 / (i : ℝ)) * ((8 / (Real.pi * ((2 * N : ℕ) : ℝ))) *
      vaughanTypeIIRectangularL1exp N k l * weightedPrimitiveFamilyMass (G.cell i)) ≤
      32 * (i : ℝ) * Real.log (4 * N + 4 : ℕ) ^ 3 := by
  let L := Real.log (4 * N + 4 : ℕ)
  have hS : G.cell i ⊆ Finset.Icc 1 (2 * i) := by
    intro q hq
    have h := Finset.mem_Ioc.mp (hcell hq)
    exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  have hm := weightedPrimitiveFamilyMass_le_triangular (2 * i) (G.cell i) hS
  have hm' : weightedPrimitiveFamilyMass (G.cell i) ≤ 3 * (i : ℝ) ^ 2 := by
    calc
      _ ≤ ((2 * i : ℕ) : ℝ) * (((2 * i : ℕ) : ℝ) + 1) / 2 := hm
      _ ≤ 3 * (i : ℝ) ^ 2 := by
        push_cast
        have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
        nlinarith
  have hL1 := allAspect_L1exp_le N u v k l hN hactive
  have hcoef : 8 / (Real.pi * ((2 * N : ℕ) : ℝ)) ≤ 4 / (3 * (N : ℝ)) := by
    push_cast
    apply (div_le_div_iff₀ (mul_pos Real.pi_pos (by positivity))
      (mul_pos (by norm_num) (by exact_mod_cast (show 0 < N by omega)))).2
    nlinarith [Real.pi_gt_three]
  calc
    _ ≤ (1 / (i : ℝ)) * ((4 / (3 * (N : ℝ))) *
        (8 * (N : ℝ) * L ^ 3) * (3 * (i : ℝ) ^ 2)) := by
      have hm0 : 0 ≤ weightedPrimitiveFamilyMass (G.cell i) := by
        unfold weightedPrimitiveFamilyMass
        positivity
      have hL10 : 0 ≤ vaughanTypeIIRectangularL1exp N k l := by
        unfold vaughanTypeIIRectangularL1exp
        positivity
      gcongr
    _ = _ := by field_simp; ring

/-- All-aspect scalar estimate for one actual active rectangle in an arbitrary
production conductor cell. -/
theorem apNormalizedVaughanActualCollectedShellMeanOn_cell_le_allAspect_scalar
    (N Q C u v k l i : ℕ) (G : ProductionConductorBlockGeometry N Q C)
    (_hiG : i ∈ G.index) (hcell : G.cell i ⊆ Finset.Ioc i (2 * i))
    (hN : 9 ≤ N) (hi : 0 < i) (h2i : 2 * i ≤ N)
    (_hu : u < N) (_hv : v < N)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    apNormalizedVaughanActualCollectedShellMeanOn N u v k l (G.cell i) ≤
      1000000 * Real.log (4 * N + 4 : ℕ) ^ 15 *
        ((N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
          (N : ℝ) / Real.sqrt (v + 1 : ℕ) + (i : ℝ) * Real.sqrt N) := by
  classical
  let L : ℝ := Real.log (4 * N + 4 : ℕ)
  let D : ℝ := vaughanTypeIIRectangularD k
  let X : ℝ := vaughanTypeIIRectangularX N k
  let A : ℝ := (N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
    (N : ℝ) / Real.sqrt (v + 1 : ℕ) + (i : ℝ) * Real.sqrt N
  have hL : 1 ≤ L := le_trans (by norm_num) (allAspect_log_ge_two N hN)
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hDX : D * X ≤ N := by
    dsimp [D, X]
    exact_mod_cast (allAspect_active_geometry N u v k l hactive).2.2
  have hcorner : 2 ^ l ≤ vaughanTypeIIRectangularX N k := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).2
    simpa [mul_comm] using (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).2
  obtain ⟨huD, hvX⟩ := allAspect_shell_lower_bounds N u v k l hactive
  have hvX' : (v + 1 : ℕ) ≤ 2 * vaughanTypeIIRectangularX N k :=
    hvX.trans (Nat.mul_le_mul_left 2 hcorner)
  -- A single symmetric root estimate pays both off-diagonal terms.
  have cross (a b w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 < w)
      (hab : a * b ≤ N) (hwb : w ≤ 2 * b) :
      a * Real.sqrt b ≤ 2 * (N : ℝ) / Real.sqrt w := by
    have hs : Real.sqrt b * Real.sqrt w ≤ 2 * b := by
      calc
        Real.sqrt b * Real.sqrt w = Real.sqrt (b * w) := (Real.sqrt_mul hb w).symm
        _ ≤ Real.sqrt ((2 * b) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [mul_le_mul_of_nonneg_left hwb hb]
        _ = 2 * b := Real.sqrt_sq (by positivity)
    apply (le_div_iff₀ (Real.sqrt_pos.2 hw)).2
    nlinarith [mul_le_mul_of_nonneg_left hs ha]
  have hcrossX : D * Real.sqrt X ≤ 2 * (N : ℝ) / Real.sqrt (v + 1 : ℕ) :=
    cross D X (v + 1 : ℕ) hD hX (by positivity) hDX (by dsimp [X]; exact_mod_cast hvX')
  have hcrossD : X * Real.sqrt D ≤ 2 * (N : ℝ) / Real.sqrt (u + 1 : ℕ) :=
    cross X D (u + 1 : ℕ) hX hD (by positivity)
      (by simpa [mul_comm] using hDX) (by dsimp [D]; exact_mod_cast huD)
  have hroots : Real.sqrt D * Real.sqrt X ≤ Real.sqrt N := by
    rw [← Real.sqrt_mul hD]
    exact Real.sqrt_le_sqrt hDX
  have hparts : (N : ℝ) / i ≤ A ∧
      (N : ℝ) / Real.sqrt (u + 1 : ℕ) ≤ A ∧
      (N : ℝ) / Real.sqrt (v + 1 : ℕ) ≤ A ∧
      (i : ℝ) * Real.sqrt N ≤ A := by
    have h0 : (0 : ℝ) ≤ (N : ℝ) / i := by positivity
    have h1 : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (u + 1 : ℕ) := by positivity
    have h2 : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (v + 1 : ℕ) := by positivity
    have h3 : (0 : ℝ) ≤ (i : ℝ) * Real.sqrt N := by positivity
    dsimp [A]
    constructor; linarith
    constructor; linarith
    constructor <;> linarith
  have hNA : (N : ℝ) ≤ (i : ℝ) * A := by
    simpa [mul_comm] using (div_le_iff₀ hiR).1 hparts.1
  have huA : (N : ℝ) / Real.sqrt (u + 1 : ℕ) ≤ A := hparts.2.1
  have hvA : (N : ℝ) / Real.sqrt (v + 1 : ℕ) ≤ A := hparts.2.2.1
  have hiA : (i : ℝ) * Real.sqrt N ≤ A := hparts.2.2.2
  have hiA' : (i : ℝ) ≤ A := by
    have hs : 1 ≤ Real.sqrt (N : ℝ) := by
      exact Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ N by omega))
    nlinarith
  have hq := allAspect_qFactor_le N i hN hi h2i
  have hq0 : 0 ≤ primitiveBilinearQFactor (2 * i) := by
    unfold primitiveBilinearQFactor
    positivity
  have hR : vaughanTypeIIRectangularRexp N k l (2 * i) ≤
      12000 * L ^ 5 * (i : ℝ) * A := by
    refine (vaughanTypeIIRectangularRexp_le_expanded_allAspect
      N (2 * i) u v k l (by omega) hactive).trans ?_
    have hroot := allAspect_root_log_le N u v k l hN hactive
    change _ ≤ 12000 * L ^ 5 * (i : ℝ) * A
    have hsum : D * Real.sqrt X + X * Real.sqrt D ≤ 4 * A := by
      simp only [mul_div_assoc] at hcrossX hcrossD
      nlinarith
    have hbody : D * X + primitiveBilinearQFactor (2 * i) * (2 * i : ℕ) *
        (D * Real.sqrt X + X * Real.sqrt D) +
        primitiveBilinearQFactor (2 * i) ^ 2 * (2 * i : ℕ) ^ 2 *
          Real.sqrt D * Real.sqrt X ≤ 2000 * L ^ 2 * (i : ℝ) * A := by
      calc
        _ ≤ (i : ℝ) * A + (15 * L) * (2 * i : ℕ) * (4 * A) +
            (15 * L) ^ 2 * (2 * i : ℕ) ^ 2 * Real.sqrt N := by
          rw [mul_assoc (_ ^ 2 * _ ^ 2)]
          apply add_le_add
          · apply add_le_add (hDX.trans hNA)
            gcongr
          · gcongr
        _ ≤ 2000 * L ^ 2 * (i : ℝ) * A := by
          push_cast
          have hlast := mul_le_mul_of_nonneg_left hiA
            (show 0 ≤ 900 * L ^ 2 * (i : ℝ) by positivity)
          have hL2 : L ≤ L ^ 2 := by nlinarith
          nlinarith [mul_nonneg (show 0 ≤ L ^ 2 - 1 by nlinarith)
            (show 0 ≤ (i : ℝ) * A by positivity),
            mul_nonneg (show 0 ≤ L ^ 2 - L by nlinarith)
            (show 0 ≤ (i : ℝ) * A by positivity)]
    calc
      _ ≤ (6 * L ^ 3) * (2000 * L ^ 2 * (i : ℝ) * A) := by
        exact mul_le_mul hroot hbody (by positivity) (by positivity)
      _ = _ := by ring
  have hS : G.cell i ⊆ Finset.Icc 1 (2 * i) := by
    intro q hqS
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp (hcell hqS)
    exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩
  have hn := apNormalizedVaughanActualCollectedShellMeanOn_le_inv_mul_weightedMean
    N u v k l i (G.cell i) hi (fun q hqS => (Finset.mem_Ioc.mp (hcell hqS)).1.le)
  have he := vaughanActualCanonicalCollectedShellWeightedMean_le_explicit
    N (2 * i) u v k l (by omega) (by omega) (G.cell i) hS hactive
  have hs := allAspect_smoothing_le N hN
  have hsharp := allAspect_sharpTerm_le N Q C u v k l i G hN hi hcell hactive
  have hLP : L ^ 6 ≤ L ^ 15 := pow_le_pow_right₀ hL (by omega)
  have hLP3 : L ^ 3 ≤ L ^ 15 := pow_le_pow_right₀ hL (by omega)
  have hmain : (1 / (i : ℝ)) *
      ((1 / 2 + (14 * Real.log (2 * N : ℕ) + 4) / Real.pi) *
        vaughanTypeIIRectangularRexp N k l (2 * i)) ≤ 96000 * L ^ 6 * A := by
    calc
      _ ≤ (1 / (i : ℝ)) * ((8 * L) * (12000 * L ^ 5 * (i : ℝ) * A)) := by
        have hR0 : 0 ≤ vaughanTypeIIRectangularRexp N k l (2 * i) := by
          unfold vaughanTypeIIRectangularRexp
          positivity
        gcongr
      _ = _ := by field_simp; ring
  have htotal := hn.trans (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1 / (i : ℝ)))
  rw [mul_add] at htotal
  change _ ≤ 1000000 * L ^ 15 * A
  have hpay := mul_le_mul_of_nonneg_right hLP hA
  have hpay3 := mul_le_mul_of_nonneg_right hLP3 hA
  have hsharp' := mul_le_mul_of_nonneg_right hiA' (show 0 ≤ L ^ 3 by positivity)
  nlinarith

/-- Summing the all-aspect estimate over every active canonical rectangle keeps
exactly the active-family cardinality. -/
theorem sum_activeRectangles_cell_le_card_mul_allAspect_scalar
    (N Q C u v i : ℕ) (G : ProductionConductorBlockGeometry N Q C)
    (hiG : i ∈ G.index) (hcell : G.cell i ⊆ Finset.Ioc i (2 * i))
    (hN : 9 ≤ N) (hi : 0 < i) (h2i : 2 * i ≤ N) (hu : u < N) (hv : v < N) :
    (∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
      apNormalizedVaughanActualCollectedShellMeanOn N u v kl.1 kl.2 (G.cell i)) ≤
      ((vaughanTypeIIActiveCanonicalRectangles N u v).card : ℝ) *
        (1000000 * Real.log (4 * N + 4 : ℕ) ^ 15 *
          ((N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
            (N : ℝ) / Real.sqrt (v + 1 : ℕ) + (i : ℝ) * Real.sqrt N)) := by
  calc
    _ ≤ ∑ _kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        1000000 * Real.log (4 * N + 4 : ℕ) ^ 15 *
          ((N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
            (N : ℝ) / Real.sqrt (v + 1 : ℕ) + (i : ℝ) * Real.sqrt N) := by
      apply Finset.sum_le_sum
      intro kl hkl
      exact apNormalizedVaughanActualCollectedShellMeanOn_cell_le_allAspect_scalar
        N Q C u v kl.1 kl.2 i G hiG hcell hN hi h2i hu hv hkl
    _ = _ := by simp

end
end AnalyticNumberTheory.LargeSieve
