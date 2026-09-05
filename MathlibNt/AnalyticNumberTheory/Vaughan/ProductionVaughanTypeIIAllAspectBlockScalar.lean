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
    have htmaj : t + c * q ^ 2 ≤ x + c * q ^ 2 := by linarith
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
  nlinarith

private lemma allAspect_root_log_le
    (N u v k l : ℕ) (hN : 9 ≤ N)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
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
    (hiG : i ∈ G.index) (hcell : G.cell i ⊆ Finset.Ioc i (2 * i))
    (hN : 9 ≤ N) (hi : 0 < i) (h2i : 2 * i ≤ N)
    (hu : u < N) (hv : v < N)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    apNormalizedVaughanActualCollectedShellMeanOn N u v k l (G.cell i) ≤
      1000000 * Real.log (4 * N + 4 : ℕ) ^ 15 *
        ((N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
          (N : ℝ) / Real.sqrt (v + 1 : ℕ) + (i : ℝ) * Real.sqrt N) := by
  let L := Real.log (4 * N + 4 : ℕ)
  let D : ℝ := vaughanTypeIIRectangularD k
  let X : ℝ := vaughanTypeIIRectangularX N k
  let c : ℝ := primitiveBilinearQFactor (2 * i)
  let rd := Real.sqrt D
  let rx := Real.sqrt X
  have hg := allAspect_active_geometry N u v k l hactive
  have hlower := allAspect_shell_lower_bounds N u v k l hactive
  have hlevels : ∀ q ∈ G.cell i, i ≤ q := fun q hq => (Finset.mem_Ioc.mp (hcell hq)).1.le
  have hS : G.cell i ⊆ Finset.Icc 1 (2 * i) := by
    intro q hq
    have h := Finset.mem_Ioc.mp (hcell hq)
    exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  have hnorm := apNormalizedVaughanActualCollectedShellMeanOn_le_inv_mul_weightedMean
    N u v k l i (G.cell i) hi hlevels
  have hexp := vaughanActualCanonicalCollectedShellWeightedMean_le_explicit
    N (2 * i) u v k l (by omega) (by omega) (G.cell i) hS hactive
  have hR := vaughanTypeIIRectangularRexp_le_expanded_allAspect
    N (2 * i) u v k l (by omega) hactive
  have hsmooth := allAspect_smoothing_le N hN
  have hroot := allAspect_root_log_le N u v k l hN hactive
  have hc := allAspect_qFactor_le N i hN hi h2i
  have hc0 : 0 ≤ c := by dsimp [c]; exact primitiveBilinearQFactor_nonneg _
  have hL2 : 2 ≤ L := allAspect_log_ge_two N hN
  have hL0 : 0 ≤ L := by linarith
  have hD0 : 0 ≤ D := by positivity
  have hX0 : 0 ≤ X := by positivity
  have hDX : D * X ≤ (N : ℝ) := by
    dsimp [D, X]
    exact_mod_cast hg.2.2
  have hrd2 : rd ^ 2 = D := Real.sq_sqrt hD0
  have hrx2 : rx ^ 2 = X := Real.sq_sqrt hX0
  have hrd0 : 0 ≤ rd := Real.sqrt_nonneg _
  have hrx0 : 0 ≤ rx := Real.sqrt_nonneg _
  have hu0 : (0 : ℝ) < (u + 1 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < (v + 1 : ℕ) := by positivity
  have hru0 : 0 < Real.sqrt (u + 1 : ℕ) := Real.sqrt_pos.2 hu0
  have hrv0 : 0 < Real.sqrt (v + 1 : ℕ) := Real.sqrt_pos.2 hv0
  have hru : Real.sqrt (u + 1 : ℕ) ≤ 2 * rd := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hcast : ((u + 1 : ℕ) : ℝ) ≤ 2 * D := by
        dsimp [D]
        exact_mod_cast hlower.1
      nlinarith
  have hrv : Real.sqrt (v + 1 : ℕ) ≤ 2 * rx := by
    have h2lX : (2 ^ l : ℝ) ≤ X := by
      dsimp [X]
      exact_mod_cast (show 2 ^ l ≤ vaughanTypeIIRectangularX N k from
        (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).2
          (by simpa [mul_comm] using
            (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).2))
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hcast : ((v + 1 : ℕ) : ℝ) ≤ 2 * (2 ^ l : ℝ) := by exact_mod_cast hlower.2
      nlinarith
  have hDroot : D * rx ≤ 2 * (N : ℝ) / Real.sqrt (v + 1 : ℕ) := by
    apply (le_div_iff₀ hrv0).2
    nlinarith [mul_nonneg hD0 hrx0]
  have hXroot : X * rd ≤ 2 * (N : ℝ) / Real.sqrt (u + 1 : ℕ) := by
    apply (le_div_iff₀ hru0).2
    nlinarith [mul_nonneg hX0 hrd0]
  have hprodroot : rd * rx ≤ Real.sqrt N := by
    have hsquares : (rd * rx) ^ 2 ≤ (Real.sqrt N) ^ 2 := by
      rw [mul_pow, hrd2, hrx2, Real.sq_sqrt (by positivity)]
      exact hDX
    nlinarith [Real.sqrt_nonneg (N : ℝ), mul_nonneg hrd0 hrx0]
  have hsharp := allAspect_sharpTerm_le N Q C u v k l i G hN hi hcell hactive
  have hsqrtN3 : 3 ≤ Real.sqrt (N : ℝ) := by
    have hh := Real.sqrt_le_sqrt (by exact_mod_cast hN : (9 : ℝ) ≤ N)
    norm_num at hh ⊢
    exact hh
  have hbase0 : 0 ≤ (N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
      (N : ℝ) / Real.sqrt (v + 1 : ℕ) + (i : ℝ) * Real.sqrt N := by positivity
  let B : ℝ := (N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
    (N : ℝ) / Real.sqrt (v + 1 : ℕ) + (i : ℝ) * Real.sqrt N
  have hB0 : 0 ≤ B := by simpa [B] using hbase0
  have hinner :
      D * X + c * ((2 * i : ℕ) : ℝ) * (D * rx + X * rd) +
          c ^ 2 * ((2 * i : ℕ) : ℝ) ^ 2 * rd * rx ≤
        (N : ℝ) + (15 * L) * (2 * (i : ℝ)) *
          (2 * (N : ℝ) / Real.sqrt (v + 1 : ℕ) +
           2 * (N : ℝ) / Real.sqrt (u + 1 : ℕ)) +
          (15 * L) ^ 2 * (4 * (i : ℝ) ^ 2) * Real.sqrt N := by
    have hc2 : c ^ 2 ≤ (15 * L) ^ 2 := pow_le_pow_left₀ hc0 hc 2
    have hcast2 : (((2 * i : ℕ) : ℝ)) = 2 * (i : ℝ) := by norm_num
    rw [hcast2]
    apply add_le_add
    · apply add_le_add hDX
      apply mul_le_mul
      · exact mul_le_mul hc (le_refl _) (by positivity) (by positivity)
      · exact add_le_add hDroot hXroot
      · positivity
      · positivity
    · calc
        c ^ 2 * (2 * (i : ℝ)) ^ 2 * rd * rx ≤
            (15 * L) ^ 2 * (2 * (i : ℝ)) ^ 2 * rd * rx := by
              calc
                _ = c ^ 2 * ((2 * (i : ℝ)) ^ 2 * rd * rx) := by ring
                _ ≤ (15 * L) ^ 2 * ((2 * (i : ℝ)) ^ 2 * rd * rx) :=
                  mul_le_mul_of_nonneg_right hc2 (by positivity)
                _ = _ := by ring
        _ ≤ (15 * L) ^ 2 * (4 * (i : ℝ) ^ 2) * Real.sqrt N := by
          rw [show (2 * (i : ℝ)) ^ 2 = 4 * (i : ℝ) ^ 2 by ring]
          calc
            _ = ((15 * L) ^ 2 * (4 * (i : ℝ) ^ 2)) * (rd * rx) := by ring
            _ ≤ ((15 * L) ^ 2 * (4 * (i : ℝ) ^ 2)) * Real.sqrt N :=
              mul_le_mul_of_nonneg_left hprodroot (by positivity)
            _ = _ := by ring
  have hmain :
      (1 / (i : ℝ)) *
        ((1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) *
          vaughanTypeIIRectangularRexp N k l (2 * i)) ≤
      (1 / (i : ℝ)) * ((8 * L) * (6 * L ^ 3) *
        ((N : ℝ) + (15 * L) * (2 * (i : ℝ)) *
          (2 * (N : ℝ) / Real.sqrt (v + 1 : ℕ) +
           2 * (N : ℝ) / Real.sqrt (u + 1 : ℕ)) +
          (15 * L) ^ 2 * (4 * (i : ℝ) ^ 2) * Real.sqrt N)) := by
    have hR' : vaughanTypeIIRectangularRexp N k l (2 * i) ≤
        (6 * L ^ 3) *
          (D * X + c * ((2 * i : ℕ) : ℝ) * (D * rx + X * rd) +
            c ^ 2 * ((2 * i : ℕ) : ℝ) ^ 2 * rd * rx) := by
      calc
        _ ≤ Real.sqrt (27 * Real.log
              (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5) *
            ((vaughanTypeIIRectangularD k : ℝ) *
                vaughanTypeIIRectangularX N k +
              primitiveBilinearQFactor (2 * i) * ((2 * i : ℕ) : ℝ) *
                ((vaughanTypeIIRectangularD k : ℝ) *
                    Real.sqrt (vaughanTypeIIRectangularX N k) +
                  (vaughanTypeIIRectangularX N k : ℝ) *
                    Real.sqrt (vaughanTypeIIRectangularD k)) +
              primitiveBilinearQFactor (2 * i) ^ 2 * ((2 * i : ℕ) : ℝ) ^ 2 *
                Real.sqrt (vaughanTypeIIRectangularD k) *
                Real.sqrt (vaughanTypeIIRectangularX N k)) := hR
        _ ≤ _ := by
          dsimp [D, X, c, rd, rx]
          gcongr
    have hR0 : 0 ≤ vaughanTypeIIRectangularRexp N k l (2 * i) := by
      unfold vaughanTypeIIRectangularRexp
      positivity
    calc
      _ ≤ (1 / (i : ℝ)) * ((8 * L) *
          vaughanTypeIIRectangularRexp N k l (2 * i)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hsmooth hR0
      _ ≤ (1 / (i : ℝ)) * ((8 * L) * ((6 * L ^ 3) *
          (D * X + c * ((2 * i : ℕ) : ℝ) * (D * rx + X * rd) +
            c ^ 2 * ((2 * i : ℕ) : ℝ) ^ 2 * rd * rx))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left hR' (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        convert mul_le_mul_of_nonneg_left hinner
          (mul_nonneg (by positivity : 0 ≤ 8 * L) (by positivity : 0 ≤ 6 * L ^ 3)) using 1 <;> ring
  calc
    _ ≤ (1 / (i : ℝ)) * vaughanActualCanonicalCollectedShellWeightedMean
        N u v k l (G.cell i) := hnorm
    _ ≤ (1 / (i : ℝ)) *
        ((1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) *
          vaughanTypeIIRectangularRexp N k l (2 * i) +
        (8 / (Real.pi * ((2 * N : ℕ) : ℝ))) *
          vaughanTypeIIRectangularL1exp N k l * weightedPrimitiveFamilyMass (G.cell i)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ (1 / (i : ℝ)) * ((8 * L) * (6 * L ^ 3) *
          ((N : ℝ) + (15 * L) * (2 * (i : ℝ)) *
            (2 * (N : ℝ) / Real.sqrt (v + 1 : ℕ) +
             2 * (N : ℝ) / Real.sqrt (u + 1 : ℕ)) +
            (15 * L) ^ 2 * (4 * (i : ℝ) ^ 2) * Real.sqrt N)) +
        32 * (i : ℝ) * L ^ 3 := by
      rw [mul_add]
      exact add_le_add hmain hsharp
    _ ≤ 1000000 * L ^ 15 *
        ((N : ℝ) / i + (N : ℝ) / Real.sqrt (u + 1 : ℕ) +
          (N : ℝ) / Real.sqrt (v + 1 : ℕ) + (i : ℝ) * Real.sqrt N) := by
      have hL1 : 1 ≤ L := by linarith
      have hpow6 : L ^ 6 ≤ L ^ 15 := pow_le_pow_right₀ hL1 (by omega)
      have hpow5 : L ^ 5 ≤ L ^ 15 := pow_le_pow_right₀ hL1 (by omega)
      have hpow4 : L ^ 4 ≤ L ^ 15 := pow_le_pow_right₀ hL1 (by omega)
      have hpow3 : L ^ 3 ≤ L ^ 15 := pow_le_pow_right₀ hL1 (by omega)
      have hsharpB : 32 * (i : ℝ) * L ^ 3 ≤ 32 * L ^ 3 * B := by
        have hiB : (i : ℝ) ≤ B := by
          have hii : (i : ℝ) ≤ (i : ℝ) * Real.sqrt N := by
            nlinarith [mul_nonneg (show (0 : ℝ) ≤ i by positivity)
              (sub_nonneg.mpr hsqrtN3)]
          dsimp [B]
          have h1 : 0 ≤ (N : ℝ) / i := by positivity
          have h2 : 0 ≤ (N : ℝ) / Real.sqrt (u + 1 : ℕ) := by positivity
          have h3 : 0 ≤ (N : ℝ) / Real.sqrt (v + 1 : ℕ) := by positivity
          linarith
        nlinarith [mul_nonneg (pow_nonneg hL0 3) (sub_nonneg.mpr hiB)]
      have hn0 : 0 ≤ (N : ℝ) / i := by positivity
      have huq0 : 0 ≤ (N : ℝ) / Real.sqrt (u + 1 : ℕ) := by positivity
      have hvq0 : 0 ≤ (N : ℝ) / Real.sqrt (v + 1 : ℕ) := by positivity
      have hir0 : 0 ≤ (i : ℝ) * Real.sqrt N := by positivity
      have hNdiv : (N : ℝ) / i ≤ B := by dsimp [B]; linarith
      have huB : (N : ℝ) / Real.sqrt (u + 1 : ℕ) ≤ B := by dsimp [B]; linarith
      have hvB : (N : ℝ) / Real.sqrt (v + 1 : ℕ) ≤ B := by dsimp [B]; linarith
      have hiB : (i : ℝ) * Real.sqrt N ≤ B := by dsimp [B]; linarith
      have hiR : (0 : ℝ) < i := by exact_mod_cast hi
      calc
        _ = 48 * L ^ 4 * ((N : ℝ) / i) +
              2880 * L ^ 5 * ((N : ℝ) / Real.sqrt (v + 1 : ℕ) +
                (N : ℝ) / Real.sqrt (u + 1 : ℕ)) +
              43200 * L ^ 6 * ((i : ℝ) * Real.sqrt N) +
              32 * (i : ℝ) * L ^ 3 := by field_simp; ring
        _ ≤ (48 * L ^ 4 + 5760 * L ^ 5 + 43200 * L ^ 6 + 32 * L ^ 3) * B := by
          nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 48) (pow_nonneg hL0 4))
              (sub_nonneg.mpr hNdiv),
            mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2880) (pow_nonneg hL0 5))
              (sub_nonneg.mpr hvB),
            mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2880) (pow_nonneg hL0 5))
              (sub_nonneg.mpr huB),
            mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 43200) (pow_nonneg hL0 6))
              (sub_nonneg.mpr hiB), sub_nonneg.mpr hsharpB]
        _ ≤ 1000000 * L ^ 15 * B := by
          apply mul_le_mul_of_nonneg_right _ hB0
          nlinarith [hpow3, hpow4, hpow5, hpow6, pow_nonneg hL0 15]
        _ = _ := by rfl

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
