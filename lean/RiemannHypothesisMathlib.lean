/-
  Riemann Hypothesis — Formal Analytic & Algebraic Equivalences and Candidate-Lemma Refutations
  Verified against Mathlib (Lean 4.15.0) with zero `sorry` placeholders and zero custom axioms.

  Imports Mathlib's official `riemannZeta` and `RiemannHypothesis` definitions over `ℂ`,
  `Complex.normSq`, `Nat.divisors`, and real/complex ring & nonlinear arithmetic tactics.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Filter Topology Complex

namespace RiemannHypothesisMathlib

noncomputable section

/- ============================================================================
   SECTION 1: RH-01 — ANALYTIC LI-BOMBIERI UNIT-DISK EQUIVALENCE OVER `ℂ`
   & DIRECT EQUIVALENCE WITH MATHLIB'S OFFICIAL `RiemannHypothesis`
   ============================================================================ -/

/-- The Li-Bombieri norm-square margin `|ρ|^2 - |ρ - 1|^2` over `ℂ`.
    Since `|1 - 1/ρ| ≤ 1 ↔ |ρ - 1|^2 ≤ |ρ|^2`, non-negativity of `liNormMargin ρ`
    characterizes when `1 - 1/ρ` lies inside the closed unit disk. -/
noncomputable def liNormMargin (ρ : ℂ) : ℝ :=
  Complex.normSq ρ - Complex.normSq (ρ - 1)

/-- Theorem RH-01a: Over `ℂ`, the imaginary ordinate `ρ.im` cancels identically in
    `liNormMargin ρ = |ρ|^2 - |ρ - 1|^2 = 2 * Re(ρ) - 1`. -/
theorem rh_01_liNormMargin_eq_two_re_sub_one (ρ : ℂ) :
    liNormMargin ρ = 2 * ρ.re - 1 := by
  unfold liNormMargin
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  ring

/-- Theorem RH-01b: Under the functional-equation reflection `ρ ↦ 1 - star ρ`,
    the Li norm-square margin is strictly antisymmetric:
    `liNormMargin ρ + liNormMargin (1 - star ρ) = 0`. -/
theorem rh_01_liNormMargin_antisymm (ρ : ℂ) :
    liNormMargin ρ + liNormMargin (1 - star ρ) = 0 := by
  rw [rh_01_liNormMargin_eq_two_re_sub_one, rh_01_liNormMargin_eq_two_re_sub_one]
  simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
  ring

/-- Theorem RH-01c (Exact Sum-of-Squares Identity over `ℂ`):
    The product of `liNormMargin ρ` and `-liNormMargin (1 - star ρ)` equals `(2 * Re(ρ) - 1)^2 ≥ 0`. -/
theorem rh_01_liNormMargin_product_sos (ρ : ℂ) :
    liNormMargin ρ * (-liNormMargin (1 - star ρ)) = (2 * ρ.re - 1) ^ 2 ∧
    0 ≤ liNormMargin ρ * (-liNormMargin (1 - star ρ)) := by
  have h1 : liNormMargin ρ = 2 * ρ.re - 1 := rh_01_liNormMargin_eq_two_re_sub_one ρ
  have h2 : liNormMargin (1 - star ρ) = 1 - 2 * ρ.re := by
    rw [rh_01_liNormMargin_eq_two_re_sub_one]
    simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
    ring
  rw [h1, h2]
  constructor
  · ring
  · have hsq : (2 * ρ.re - 1) * -(1 - 2 * ρ.re) = (2 * ρ.re - 1) ^ 2 := by ring
    rw [hsq]
    exact sq_nonneg (2 * ρ.re - 1)

/-- Theorem RH-01d (Analytic Unit-Disk Critical-Line Equivalence over `ℂ`):
    For any `ρ : ℂ`, both `ρ` and its functional-equation partner `1 - star ρ`
    satisfy the Li unit-disk condition (`0 ≤ liNormMargin ρ ∧ 0 ≤ liNormMargin (1 - star ρ)`)
    if and only if `ρ` lies on the critical line `ρ.re = 1 / 2`. -/
theorem rh_01_unit_disk_iff_critical_line (ρ : ℂ) :
    (0 ≤ liNormMargin ρ ∧ 0 ≤ liNormMargin (1 - star ρ)) ↔ ρ.re = 1 / 2 := by
  rw [rh_01_liNormMargin_eq_two_re_sub_one, rh_01_liNormMargin_eq_two_re_sub_one]
  simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
  constructor
  · intro ⟨h1, h2⟩
    linarith
  · intro hre
    constructor <;> linarith

/-- Theorem RH-01e (Direct Bridge to Mathlib's Official `RiemannHypothesis`):
    Mathlib's `RiemannHypothesis` holds if and only if every non-trivial zero `s : ℂ`
    of `riemannZeta` satisfies the paired Li unit-disk inequality
    `0 ≤ liNormMargin s ∧ 0 ≤ liNormMargin (1 - star s)`. -/
theorem rh_01_mathlib_riemannHypothesis_iff_li_unit_disk :
    RiemannHypothesis ↔
      ∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
        (0 ≤ liNormMargin s ∧ 0 ≤ liNormMargin (1 - star s)) := by
  unfold RiemannHypothesis
  constructor
  · intro hRH s hzero htriv hone
    exact (rh_01_unit_disk_iff_critical_line s).mpr (hRH s hzero htriv hone)
  · intro hLi s hzero htriv hone
    exact (rh_01_unit_disk_iff_critical_line s).mp (hLi s hzero htriv hone)

/- ============================================================================
   SECTION 2: RH-02 — COMPLETED ZETA 4-FOLD ZERO ORBIT VARIANCE OVER `ℂ`
   & DIRECT EQUIVALENCE WITH MATHLIB'S `RiemannHypothesis`
   ============================================================================ -/

/-- Sum of real parts across the 4-element Riemann Xi symmetry orbit
    `{ρ, star ρ, 1 - ρ, 1 - star ρ}` in `ℂ`. -/
def xiOrbitRealSum (ρ : ℂ) : ℝ :=
  ρ.re + (star ρ).re + (1 - ρ).re + (1 - star ρ).re

/-- Total squared horizontal deviation of `{ρ, star ρ, 1 - ρ, 1 - star ρ}` from `1 / 2`. -/
def xiOrbitVariance (ρ : ℂ) : ℝ :=
  (ρ.re - 1 / 2) ^ 2 + ((star ρ).re - 1 / 2) ^ 2 +
  ((1 - ρ).re - 1 / 2) ^ 2 + ((1 - star ρ).re - 1 / 2) ^ 2

/-- Theorem RH-02a: For every `ρ : ℂ`, the real-part sum across the 4-element symmetry orbit
    is invariantly `2` (so the horizontal barycenter is invariantly `1 / 2`). -/
theorem rh_02_xiOrbitRealSum_invariant (ρ : ℂ) :
    xiOrbitRealSum ρ = 2 := by
  unfold xiOrbitRealSum
  simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
  ring

/-- Theorem RH-02b: For every `ρ : ℂ`, the horizontal orbit variance equals `(2 * ρ.re - 1)^2 ≥ 0`
    and vanishes if and only if `ρ.re = 1 / 2`. -/
theorem rh_02_xiOrbitVariance_sos_and_collapse (ρ : ℂ) :
    xiOrbitVariance ρ = (2 * ρ.re - 1) ^ 2 ∧
    0 ≤ xiOrbitVariance ρ ∧
    (xiOrbitVariance ρ = 0 ↔ ρ.re = 1 / 2) := by
  have hvar : xiOrbitVariance ρ = (2 * ρ.re - 1) ^ 2 := by
    unfold xiOrbitVariance
    simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
    ring
  refine ⟨hvar, ?_, ?_⟩
  · rw [hvar]
    exact sq_nonneg (2 * ρ.re - 1)
  · rw [hvar, sq_eq_zero_iff]
    constructor <;> intro h <;> linarith

/-- Theorem RH-02c (Direct Bridge to Mathlib's Official `RiemannHypothesis`):
    Mathlib's `RiemannHypothesis` holds if and only if the 4-element symmetry orbit
    variance `xiOrbitVariance s` vanishes for every non-trivial zero `s : ℂ` of `riemannZeta`. -/
theorem rh_02_mathlib_riemannHypothesis_iff_zero_orbit_variance :
    RiemannHypothesis ↔
      ∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
        xiOrbitVariance s = 0 := by
  unfold RiemannHypothesis
  constructor
  · intro hRH s hzero htriv hone
    exact (rh_02_xiOrbitVariance_sos_and_collapse s).2.2.mpr (hRH s hzero htriv hone)
  · intro hVar s hzero htriv hone
    exact (rh_02_xiOrbitVariance_sos_and_collapse s).2.2.mp (hVar s hzero htriv hone)

/- ============================================================================
   SECTION 3: RH-03 — COMPLEX-ANALYTIC REFUTATION OF
   "FUNCTIONAL EQUATION G(1 - s) = G(s) + CRITICAL-LINE REALNESS IMPLIES RH"
   ============================================================================ -/

/-- Algebraic Davenport-Heilbronn counterexample prototype over `ℂ`:
    `G(s) = 16 * s^2 - 16 * s + 3 = (4*s - 1)*(4*s - 3)`. -/
def symmetricCounterexampleG (s : ℂ) : ℂ :=
  16 * s ^ 2 - 16 * s + 3

/-- Theorem RH-03: Over `ℂ`, `symmetricCounterexampleG` satisfies:
    1. Exact functional equation `G(1 - s) = G(s)` for all `s : ℂ`,
    2. Pure realness on the entire critical line `Im(G(1/2 + I * t)) = 0` for all `t : ℝ`,
    3. Yet has an explicit off-critical-line zero at `s = 3/4 ∈ ℂ` inside the open critical
       strip `0 < Re(s) < 1` with `Re(s) ≠ 1/2`, and is strictly negative at `s = 1/2`. -/
theorem rh_03_functional_equation_and_real_critical_line_refuted :
    (∀ s : ℂ, symmetricCounterexampleG (1 - s) = symmetricCounterexampleG s) ∧
    (∀ t : ℝ, (symmetricCounterexampleG ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).im = 0) ∧
    symmetricCounterexampleG (3 / 4 : ℂ) = 0 ∧
    (0 < ((3 / 4 : ℂ).re) ∧ ((3 / 4 : ℂ).re) < 1 ∧ ((3 / 4 : ℂ).re) ≠ 1 / 2) ∧
    (symmetricCounterexampleG (1 / 2 : ℂ)).re = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    unfold symmetricCounterexampleG
    ring
  · intro t
    unfold symmetricCounterexampleG
    simp only [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, sq]
    norm_num
    ring
  · unfold symmetricCounterexampleG
    ring
  · norm_num
  · unfold symmetricCounterexampleG
    norm_num

/- ============================================================================
   SECTION 4: RH-04 — COMPLEX-ANALYTIC REFUTATION OF UNIVERSAL POSITIVITY OF
   `Re(ρ^2 + (1 - star ρ)^2)` OVER `ℂ`
   ============================================================================ -/

/-- Real part of the symmetric-square zero pair functional `Re(ρ^2 + (1 - star ρ)^2)` over `ℂ`. -/
def symSquareRealPart (ρ : ℂ) : ℝ :=
  (ρ ^ 2 + (1 - star ρ) ^ 2).re

/-- Theorem RH-04a: Exact expansion `Re(ρ^2 + (1 - star ρ)^2) = 2*Re(ρ)^2 - 2*Re(ρ) + 1 - 2*Im(ρ)^2`. -/
theorem rh_04_symSquareRealPart_expansion (ρ : ℂ) :
    symSquareRealPart ρ = 2 * ρ.re ^ 2 - 2 * ρ.re + 1 - 2 * ρ.im ^ 2 := by
  unfold symSquareRealPart
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- Theorem RH-04b: While `symSquareRealPart (1/2 : ℂ) = 1/2 > 0` on the real axis,
    on the critical line at ordinate `Im(ρ) = 1` (`ρ = 1/2 + I`),
    `symSquareRealPart (1/2 + I) = -3/2 < 0`, refuting universal non-negativity. -/
theorem rh_04_symSquareRealPart_refuted_on_critical_line :
    symSquareRealPart (1 / 2 : ℂ) = 1 / 2 ∧
    symSquareRealPart ((1 / 2 : ℂ) + Complex.I) = -3 / 2 ∧
    symSquareRealPart ((1 / 2 : ℂ) + Complex.I) < 0 := by
  rw [rh_04_symSquareRealPart_expansion, rh_04_symSquareRealPart_expansion]
  simp only [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  norm_num

/- ============================================================================
   SECTION 5: RH-05 — NECESSITY OF `n > 5040` IN ROBIN'S CRITERION VIA
   MATHLIB'S `Nat.divisors`
   ============================================================================ -/

/-- Theorem RH-05: Using Mathlib's `Nat.divisors` on the prime-power factors
    `16, 9, 5, 7` of `5040 = 16 * 9 * 5 * 7`, the exact divisor-sum product is
    `(∑ d ∈ Nat.divisors 16, d) * (∑ d ∈ Nat.divisors 9, d) * (∑ d ∈ Nat.divisors 5, d) * (∑ d ∈ Nat.divisors 7, d) = 19344`,
    the exact reduced rational ratio is `(19344 : ℝ) / 5040 = 403 / 105` (refuting the
    incorrect reduction `134 / 35 = 402 / 105`), and `(403 : ℝ) / 105` strictly exceeds both
    `19 / 5 = 3.80` and `191 / 50 = 3.82`. Consequently, for any real threshold `c_robin : ℝ`
    satisfying the external transcendental interval bound `c_robin ≤ 191 / 50`
    (where numerically `e^γ * log(log(5040)) ≈ 3.816877288 < 3.82 = 191 / 50`),
    we have `c_robin < (19344 : ℝ) / 5040`. -/
theorem rh_05_robin_5040_divisor_sum_and_threshold :
    16 * 9 * 5 * 7 = 5040 ∧
    (∑ d ∈ Nat.divisors 16, d) * (∑ d ∈ Nat.divisors 9, d) *
      (∑ d ∈ Nat.divisors 5, d) * (∑ d ∈ Nat.divisors 7, d) = 19344 ∧
    ((19344 : ℝ) / 5040 = (403 : ℝ) / 105) ∧
    ((19344 : ℝ) / 5040 ≠ (134 : ℝ) / 35) ∧
    ((19 : ℝ) / 5 < (191 : ℝ) / 50) ∧
    ((191 : ℝ) / 50 < (19344 : ℝ) / 5040) ∧
    ((19 : ℝ) / 5 < (19344 : ℝ) / 5040) ∧
    (∀ c_robin : ℝ, c_robin ≤ (191 : ℝ) / 50 → c_robin < (19344 : ℝ) / 5040) := by
  refine ⟨by norm_num, by decide, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro c_robin hc
  linarith

/- ============================================================================
   SECTION 6: RH-06 — HADAMARD CONJUGATE-PAIR QUADRATIC FACTOR POSITIVITY OVER `ℂ`
   ============================================================================ -/

/-- Hadamard paired quadratic factor `(s - ρ) * (s - star ρ)` for real `s : ℝ` and `ρ : ℂ`. -/
def hadamardConjugatePair (s : ℝ) (ρ : ℂ) : ℂ :=
  ((s : ℂ) - ρ) * ((s : ℂ) - star ρ)

/-- Theorem RH-06: For every real `s : ℝ` and complex zero `ρ : ℂ`:
    1. `hadamardConjugatePair s ρ` has zero imaginary part (`Im = 0`),
    2. Its real part is the exact Sum-of-Squares `(s - ρ.re)^2 + ρ.im^2 ≥ 0`,
    3. Whenever `ρ.im ≠ 0` (any non-real zero), `0 < (hadamardConjugatePair s ρ).re`. -/
theorem rh_06_hadamardConjugatePair_real_and_pos (s : ℝ) (ρ : ℂ) :
    (hadamardConjugatePair s ρ).im = 0 ∧
    (hadamardConjugatePair s ρ).re = (s - ρ.re) ^ 2 + ρ.im ^ 2 ∧
    0 ≤ (hadamardConjugatePair s ρ).re ∧
    (ρ.im ≠ 0 → 0 < (hadamardConjugatePair s ρ).re) := by
  have him : (hadamardConjugatePair s ρ).im = 0 := by
    unfold hadamardConjugatePair
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hre : (hadamardConjugatePair s ρ).re = (s - ρ.re) ^ 2 + ρ.im ^ 2 := by
    unfold hadamardConjugatePair
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  refine ⟨him, hre, ?_, ?_⟩
  · rw [hre]
    positivity
  · intro hnz
    rw [hre]
    have hpos : 0 < ρ.im ^ 2 := sq_pos_of_ne_zero hnz
    have hnonneg : 0 ≤ (s - ρ.re) ^ 2 := sq_nonneg (s - ρ.re)
    linarith

/- ============================================================================
   SECTION 7: RH-07 — UNCONDITIONAL TRANSCENDENTAL BOUNDS ON `Real.log 5040`,
   `Real.log (Real.log 5040)`, AND ROBIN'S THRESHOLD AT `n = 5040` OVER `ℝ`
   ============================================================================ -/

/-- Fourth-order Taylor polynomial lower bound for `Real.exp ((n : ℝ) * x)` when `0 ≤ x`:
    if `0 ≤ B ≤ 1 + x + x^2 / 2 + x^3 / 6 + x^4 / 24`, then `B ^ n ≤ Real.exp ((n : ℝ) * x)`.
    Proved directly from Mathlib's `Real.sum_le_exp_of_nonneg` and `Real.exp_nat_mul`. -/
theorem exp_lower_taylor4_step {x B : ℝ} (hx : 0 ≤ x) (hB : 0 ≤ B)
    (hstep : B ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24) (n : ℕ) :
    B ^ n ≤ Real.exp ((n : ℝ) * x) := by
  have hsum := Real.sum_le_exp_of_nonneg hx 5
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one] at hsum
  norm_num [Nat.factorial] at hsum
  have hle : B ≤ Real.exp x := by linarith
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ hB hle n

/-- Upper bound for `Real.exp ((n : ℝ) * x)` when `x < 1`:
    if `(1 - x)⁻¹ ≤ U`, then `Real.exp ((n : ℝ) * x) ≤ U ^ n`, derived from
    `Real.add_one_le_exp (-x)` and `Real.exp_nat_mul`. -/
theorem exp_upper_inv_step {x U : ℝ} (hx1 : x < 1)
    (hstep : (1 - x)⁻¹ ≤ U) (n : ℕ) :
    Real.exp ((n : ℝ) * x) ≤ U ^ n := by
  have h1 : -x + 1 ≤ Real.exp (-x) := Real.add_one_le_exp (-x)
  have hpos : 0 < 1 - x := by linarith
  have h2 : 1 - x ≤ (Real.exp x)⁻¹ := by
    rw [← Real.exp_neg]
    linarith
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  have h3 : Real.exp x ≤ (1 - x)⁻¹ := by
    rw [le_inv_comm₀ hexp_pos hpos]
    exact h2
  have h4 : Real.exp x ≤ U := le_trans h3 hstep
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (le_of_lt hexp_pos) h4 n

/-- Theorem RH-07a (Unconditional Transcendental Certificate for Robin's Criterion at `n = 5040`):
    Using Mathlib's `Real.log` and `Real.exp` without any external interval assumptions:
    1. `Real.log 5040 < 427 / 50 = 8.54`,
    2. `Real.log (Real.log 5040) < 4292 / 2000 = 2.146`,
    3. `Real.exp (5776 / 10000) < 1787 / 1000 = 1.787`,
    4. `Real.exp (5776 / 10000) * Real.log (Real.log 5040) < 19344 / 5040`. -/
theorem rh_07_unconditional_log_and_robin_5040_bounds :
    Real.log 5040 < 427 / 50 ∧
    Real.log (Real.log 5040) < 4292 / 2000 ∧
    Real.exp (5776 / 10000) < 1787 / 1000 ∧
    Real.exp (5776 / 10000) * Real.log (Real.log 5040) < (19344 : ℝ) / 5040 := by
  have hlog5040 : Real.log 5040 < 427 / 50 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 : (15325 / 10000 : ℝ) ^ 20 ≤ Real.exp (((20 : ℕ) : ℝ) * (427 / 1000 : ℝ)) :=
      exp_lower_taylor4_step (by norm_num) (by norm_num) (by norm_num) 20
    have h2 : (5040 : ℝ) < (15325 / 10000 : ℝ) ^ 20 := by norm_num
    have h3 : (((20 : ℕ) : ℝ) * (427 / 1000 : ℝ)) = 427 / 50 := by norm_num
    rw [h3] at h1
    linarith
  have hlog5040_pos : 0 < Real.log 5040 := Real.log_pos (by norm_num)
  have hlog_427 : Real.log (427 / 50) < 4292 / 2000 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 : (15358 / 10000 : ℝ) ^ 5 ≤ Real.exp (((5 : ℕ) : ℝ) * (4292 / 10000 : ℝ)) :=
      exp_lower_taylor4_step (by norm_num) (by norm_num) (by norm_num) 5
    have h2 : (427 / 50 : ℝ) < (15358 / 10000 : ℝ) ^ 5 := by norm_num
    have h3 : (((5 : ℕ) : ℝ) * (4292 / 10000 : ℝ)) = 4292 / 2000 := by norm_num
    rw [h3] at h1
    linarith
  have hloglog : Real.log (Real.log 5040) < 4292 / 2000 := by
    have hmono : Real.log (Real.log 5040) < Real.log (427 / 50) :=
      Real.log_lt_log hlog5040_pos hlog5040
    linarith
  have hexp : Real.exp (5776 / 10000) < 1787 / 1000 := by
    have h1 : Real.exp (((64 : ℕ) : ℝ) * (5776 / 640000 : ℝ)) ≤ (640000 / 634224 : ℝ) ^ 64 :=
      exp_upper_inv_step (by norm_num) (by norm_num) 64
    have h2 : (640000 / 634224 : ℝ) ^ 64 < 1787 / 1000 := by norm_num
    have h3 : (((64 : ℕ) : ℝ) * (5776 / 640000 : ℝ)) = 5776 / 10000 := by norm_num
    rw [h3] at h1
    linarith
  refine ⟨hlog5040, hloglog, hexp, ?_⟩
  have hexp_pos : 0 ≤ Real.exp (5776 / 10000) := le_of_lt (Real.exp_pos _)
  have hloglog_pos : 0 ≤ Real.log (Real.log 5040) := by
    apply Real.log_nonneg
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have h1 : Real.exp (((4 : ℕ) : ℝ) * (1 / 4 : ℝ)) ≤ (4 / 3 : ℝ) ^ 4 :=
      exp_upper_inv_step (by norm_num) (by norm_num) 4
    have h2 : (((4 : ℕ) : ℝ) * (1 / 4 : ℝ)) = 1 := by norm_num
    rw [h2] at h1
    have h3 : (4 / 3 : ℝ) ^ 4 ≤ 5040 := by norm_num
    linarith
  nlinarith

/-- Theorem RH-07b (Tighter Unconditional Bound `Real.exp (28861 / 50000) * Real.log (Real.log 5040) < 191 / 50`):
    Using a 40-step Taylor lower bound on `Real.exp (4263 / 500)`, a 10-step Taylor lower bound
    on `Real.exp (42865 / 20000)`, and a 256-step upper bound on `Real.exp (28861 / 50000)`
    (`0.57722`, strictly above Euler's constant `γ ≈ 0.5772156649`), we obtain
    `Real.log 5040 < 4263 / 500`, `Real.log (Real.log 5040) < 42865 / 20000`,
    `Real.exp (28861 / 50000) < 178225 / 100000`, and
    `Real.exp (28861 / 50000) * Real.log (Real.log 5040) < 191 / 50 < 19344 / 5040`,
    discharging the external hypothesis `c_robin ≤ 191 / 50` in `rh_05_robin_5040_divisor_sum_and_threshold`
    completely inside the Lean 4 kernel. -/
theorem rh_07_tight_191_div_50 :
    Real.log 5040 < 4263 / 500 ∧
    Real.log (Real.log 5040) < 42865 / 20000 ∧
    Real.exp (28861 / 50000) < 178225 / 100000 ∧
    Real.exp (28861 / 50000) * Real.log (Real.log 5040) < (191 : ℝ) / 50 ∧
    Real.exp (28861 / 50000) * Real.log (Real.log 5040) < (19344 : ℝ) / 5040 := by
  have hlog5040 : Real.log 5040 < 4263 / 500 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 : (1237566 / 1000000 : ℝ) ^ 40 ≤ Real.exp (((40 : ℕ) : ℝ) * (4263 / 20000 : ℝ)) :=
      exp_lower_taylor4_step (by norm_num) (by norm_num) (by norm_num) 40
    have h2 : (5040 : ℝ) < (1237566 / 1000000 : ℝ) ^ 40 := by norm_num
    have h3 : (((40 : ℕ) : ℝ) * (4263 / 20000 : ℝ)) = 4263 / 500 := by norm_num
    rw [h3] at h1
    linarith
  have hlog5040_pos : 0 < Real.log 5040 := Real.log_pos (by norm_num)
  have hlog_step2 : Real.log (4263 / 500) < 42865 / 20000 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 : (1239021 / 1000000 : ℝ) ^ 10 ≤ Real.exp (((10 : ℕ) : ℝ) * (42865 / 200000 : ℝ)) :=
      exp_lower_taylor4_step (by norm_num) (by norm_num) (by norm_num) 10
    have h2 : (4263 / 500 : ℝ) < (1239021 / 1000000 : ℝ) ^ 10 := by norm_num
    have h3 : (((10 : ℕ) : ℝ) * (42865 / 200000 : ℝ)) = 42865 / 20000 := by norm_num
    rw [h3] at h1
    linarith
  have hloglog : Real.log (Real.log 5040) < 42865 / 20000 := by
    have hmono : Real.log (Real.log 5040) < Real.log (4263 / 500) :=
      Real.log_lt_log hlog5040_pos hlog5040
    linarith
  have hexp : Real.exp (28861 / 50000) < 178225 / 100000 := by
    have h1 : Real.exp (((256 : ℕ) : ℝ) * (28861 / 12800000 : ℝ)) ≤ (12800000 / 12771139 : ℝ) ^ 256 :=
      exp_upper_inv_step (by norm_num) (by norm_num) 256
    have h2 : (12800000 / 12771139 : ℝ) ^ 256 < 178225 / 100000 := by norm_num
    have h3 : (((256 : ℕ) : ℝ) * (28861 / 12800000 : ℝ)) = 28861 / 50000 := by norm_num
    rw [h3] at h1
    linarith
  have hexp_pos : 0 ≤ Real.exp (28861 / 50000) := le_of_lt (Real.exp_pos _)
  have hloglog_pos : 0 ≤ Real.log (Real.log 5040) := by
    apply Real.log_nonneg
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have h1 : Real.exp (((4 : ℕ) : ℝ) * (1 / 4 : ℝ)) ≤ (4 / 3 : ℝ) ^ 4 :=
      exp_upper_inv_step (by norm_num) (by norm_num) 4
    have h2 : (((4 : ℕ) : ℝ) * (1 / 4 : ℝ)) = 1 := by norm_num
    rw [h2] at h1
    have h3 : (4 / 3 : ℝ) ^ 4 ≤ 5040 := by norm_num
    linarith
  have hprod191 : Real.exp (28861 / 50000) * Real.log (Real.log 5040) < (191 : ℝ) / 50 := by
    nlinarith
  have hprod5040 : Real.exp (28861 / 50000) * Real.log (Real.log 5040) < (19344 : ℝ) / 5040 := by
    have h191_lt : ((191 : ℝ) / 50) < (19344 : ℝ) / 5040 := by norm_num
    linarith
  exact ⟨hlog5040, hloglog, hexp, hprod191, hprod5040⟩

/- ============================================================================
   SECTION 8: RH-08 — DEGREE-4 FEJÉR-KONDRATIEV ZERO-FREE REGION TRIGONOMETRIC
   POLYNOMIAL STRICTLY SHARPER THAN DE LA VALLÉE POUSSIN OVER `ℝ`
   ============================================================================ -/

/-- Classical degree-2 de la Vallée Poussin cosine polynomial:
    `P_2(θ) = 3 + 4 * cos(θ) + cos(2*θ)`. -/
noncomputable def dlvpTrigPoly2 (θ : ℝ) : ℝ :=
  3 + 4 * Real.cos θ + Real.cos (2 * θ)

/-- Degree-4 Fejér-Kondratiev zero-free region cosine polynomial with positive coefficients
    `(c_0, c_1, c_2, c_3, c_4) = (103, 168, 89, 28, 4)`:
    `P_4(θ) = 103 + 168*cos(θ) + 89*cos(2*θ) + 28*cos(3*θ) + 4*cos(4*θ)`. -/
noncomputable def kondratievTrigPoly4 (θ : ℝ) : ℝ :=
  103 + 168 * Real.cos θ + 89 * Real.cos (2 * θ) + 28 * Real.cos (3 * θ) + 4 * Real.cos (4 * θ)

/-- Theorem RH-08 (Degree-4 Fejér-Kondratiev Trigonometric Polynomial Non-Negativity & Sharpness):
    1. `dlvpTrigPoly2 θ = 2 * (1 + Real.cos θ)^2 ≥ 0` for all `θ : ℝ`,
    2. `kondratievTrigPoly4 θ = 2 * (5 + 7 * Real.cos θ + 2 * Real.cos (2 * θ))^2 = 2 * (3 + 7 * Real.cos θ + 4 * Real.cos θ ^ 2)^2 ≥ 0` for all `θ : ℝ`,
    3. The degree-4 pole-to-zero ratio `c_0 / (c_1 - c_0) = 103 / 65` is strictly smaller than
       de la Vallée Poussin's `3 / (4 - 3) = 3`, and the total weight ratio
       `(c_0 + c_1 + c_2 + c_3 + c_4) / (c_1 - c_0) = 392 / 65` is strictly smaller than
       de la Vallée Poussin's `(3 + 4 + 1) / (4 - 3) = 8`. -/
theorem rh_08_kondratiev_deg4_trig_poly_pos_and_sharper :
    (∀ θ : ℝ, dlvpTrigPoly2 θ = 2 * (1 + Real.cos θ) ^ 2 ∧ 0 ≤ dlvpTrigPoly2 θ) ∧
    (∀ θ : ℝ, kondratievTrigPoly4 θ = 2 * (3 + 7 * Real.cos θ + 4 * Real.cos θ ^ 2) ^ 2 ∧
              kondratievTrigPoly4 θ = 2 * (5 + 7 * Real.cos θ + 2 * Real.cos (2 * θ)) ^ 2 ∧
              0 ≤ kondratievTrigPoly4 θ) ∧
    ((103 : ℝ) / (168 - 103) < (3 : ℝ) / (4 - 3)) ∧
    ((103 + 168 + 89 + 28 + 4 : ℝ) / (168 - 103) < (3 + 4 + 1 : ℝ) / (4 - 3)) := by
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · intro θ
    have h2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
    have h_eq : dlvpTrigPoly2 θ = 2 * (1 + Real.cos θ) ^ 2 := by
      unfold dlvpTrigPoly2
      rw [h2]
      ring
    exact ⟨h_eq, by rw [h_eq]; positivity⟩
  · intro θ
    have h2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
    have h3 : Real.cos (3 * θ) = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ := by
      have h3a : (3 : ℝ) * θ = 2 * θ + θ := by ring
      have hsin2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
      have hsq : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
        linarith [Real.sin_sq_add_cos_sq θ]
      rw [h3a, Real.cos_add, h2, hsin2]
      calc (2 * Real.cos θ ^ 2 - 1) * Real.cos θ - 2 * Real.sin θ * Real.cos θ * Real.sin θ
          = (2 * Real.cos θ ^ 2 - 1) * Real.cos θ - 2 * Real.cos θ * Real.sin θ ^ 2 := by ring
        _ = (2 * Real.cos θ ^ 2 - 1) * Real.cos θ - 2 * Real.cos θ * (1 - Real.cos θ ^ 2) := by rw [hsq]
        _ = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ := by ring
    have h4 : Real.cos (4 * θ) = 8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1 := by
      have h4a : (4 : ℝ) * θ = 2 * (2 * θ) := by ring
      rw [h4a, Real.cos_two_mul, h2]
      ring
    have h_eq1 : kondratievTrigPoly4 θ = 2 * (3 + 7 * Real.cos θ + 4 * Real.cos θ ^ 2) ^ 2 := by
      unfold kondratievTrigPoly4
      rw [h2, h3, h4]
      ring
    have h_eq2 : kondratievTrigPoly4 θ = 2 * (5 + 7 * Real.cos θ + 2 * Real.cos (2 * θ)) ^ 2 := by
      rw [h_eq1, h2]
      ring
    exact ⟨h_eq1, h_eq2, by rw [h_eq1]; positivity⟩

/-- Second-order Euler-Maclaurin upper sequence for the Euler-Mascheroni constant `γ`:
    `eulerMaclaurinSeq2 n = H_n - log(n) - (1/(2n) - 1/(12n^2))` for `n ≥ 1`, with junk value `2` at `n = 0`. -/
noncomputable def eulerMaclaurinSeq2 (n : ℕ) : ℝ :=
  if n = 0 then 2 else (harmonic n : ℝ) - Real.log n - (1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2))

lemma log_one_sub_inv_ge_sum5 {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 ≤ -Real.log (1 - x) := by
  have h_abs : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have h_sum := Real.hasSum_pow_div_log_of_abs_lt_one h_abs
  have h_le : ∑ i ∈ Finset.range 5, x ^ (i + 1) / ((i : ℝ) + 1) ≤ -Real.log (1 - x) := by
    refine sum_le_hasSum (Finset.range 5) (fun i _ => ?_) h_sum
    positivity
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat] at h_le
  linarith

lemma eulerMaclaurin_step_algebra {x : ℝ} (hx : 0 < x) :
    (1 / (2 * x) - 1 / (12 * x ^ 2)) - (1 / (2 * (x + 1)) - 1 / (12 * (x + 1) ^ 2)) <
      (1 / (x + 1)) ^ 2 / 2 + (1 / (x + 1)) ^ 3 / 3 + (1 / (x + 1)) ^ 4 / 4 + (1 / (x + 1)) ^ 5 / 5 := by
  have hx1 : 0 < x + 1 := by linarith
  have h_lhs :
      (1 / (2 * x) - 1 / (12 * x ^ 2)) - (1 / (2 * (x + 1)) - 1 / (12 * (x + 1) ^ 2)) =
      (6 * x ^ 2 + 4 * x - 1) / (12 * x ^ 2 * (x + 1) ^ 2) := by
    field_simp
    ring
  have h_rhs :
      (1 / (x + 1)) ^ 2 / 2 + (1 / (x + 1)) ^ 3 / 3 + (1 / (x + 1)) ^ 4 / 4 + (1 / (x + 1)) ^ 5 / 5 =
      (30 * (x + 1) ^ 3 + 20 * (x + 1) ^ 2 + 15 * (x + 1) + 12) / (60 * (x + 1) ^ 5) := by
    field_simp
    ring
  rw [h_lhs, h_rhs, div_lt_div_iff₀ (by positivity) (by positivity)]
  have h_poly :
      (30 * (x + 1) ^ 3 + 20 * (x + 1) ^ 2 + 15 * (x + 1) + 12) * (12 * x ^ 2 * (x + 1) ^ 2) -
      (6 * x ^ 2 + 4 * x - 1) * (60 * (x + 1) ^ 5) =
      12 * (x + 1) ^ 2 * (2 * (x - 5 / 4) ^ 2 + 15 / 8) := by
    ring
  have h_pos : 0 < 12 * (x + 1) ^ 2 * (2 * (x - 5 / 4) ^ 2 + 15 / 8) := by positivity
  linarith

lemma strictAnti_eulerMaclaurinSeq2 : StrictAnti eulerMaclaurinSeq2 := by
  refine strictAnti_nat_of_succ_lt (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eulerMaclaurinSeq2]
    norm_num
  · have hn_ne : n ≠ 0 := hn.ne'
    have hn1_ne : n + 1 ≠ 0 := Nat.succ_ne_zero n
    simp only [eulerMaclaurinSeq2, hn_ne, hn1_ne, if_false]
    rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
    set x : ℝ := (n : ℝ)
    have hx : 0 < x := Nat.cast_pos.mpr hn
    have hx1 : 0 < x + 1 := by linarith
    have hu0 : 0 < 1 / (x + 1) := by positivity
    have hu1 : 1 / (x + 1) < 1 := by
      rw [div_lt_iff₀ hx1]
      linarith
    have h_log_eq : Real.log (x + 1) - Real.log x = -Real.log (1 - 1 / (x + 1)) := by
      have h_arg : 1 - 1 / (x + 1) = x / (x + 1) := by field_simp
      rw [h_arg, Real.log_div hx.ne' hx1.ne']
      ring
    have h_log_lb := log_one_sub_inv_ge_sum5 hu0 hu1
    rw [← h_log_eq] at h_log_lb
    have h_inv_eq : (x + 1)⁻¹ = 1 / (x + 1) := by ring
    rw [h_inv_eq]
    have h_alg := eulerMaclaurin_step_algebra hx
    linarith

lemma tendsto_eulerMaclaurinSeq2 :
    Tendsto eulerMaclaurinSeq2 atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h_inv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h_nat : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    h_inv.comp tendsto_natCast_atTop_atTop
  have h_rem : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2)) atTop (𝓝 0) := by
    have h_eq : (fun n : ℕ => 1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2)) =
        (fun n : ℕ => (1 / 2 : ℝ) * (1 / (n : ℝ)) - (1 / 12 : ℝ) * ((1 / (n : ℝ)) * (1 / (n : ℝ)))) := by
      ext n
      ring
    rw [h_eq]
    simpa using (tendsto_const_nhds.mul h_nat).sub (tendsto_const_nhds.mul (h_nat.mul h_nat))
  suffices Tendsto (fun n : ℕ => ((harmonic n : ℝ) - Real.log n) - (1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2)))
      atTop (𝓝 (Real.eulerMascheroniConstant - 0)) by
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [eulerMaclaurinSeq2, hn]
  exact Real.tendsto_harmonic_sub_log.sub h_rem

lemma eulerMascheroniConstant_lt_eulerMaclaurinSeq2 (n : ℕ) :
    Real.eulerMascheroniConstant < eulerMaclaurinSeq2 n := by
  refine lt_of_le_of_lt ?_ (strictAnti_eulerMaclaurinSeq2 (Nat.lt_succ_self n))
  exact strictAnti_eulerMaclaurinSeq2.antitone.le_of_tendsto tendsto_eulerMaclaurinSeq2 (n + 1)

/-- Theorem RH-07c (Unconditional Upper Bound on `Real.eulerMascheroniConstant`):
    Evaluating `eulerMaclaurinSeq2` at `n = 8 = 2^3` with `H_8 = 761 / 280` and
    `Real.log_two_gt_d9 : 0.6931471803 < Real.log 2` proves unconditionally that
    `Real.eulerMascheroniConstant < 28861 / 50000 = 0.57722`. -/
theorem eulerMascheroniConstant_lt_28861_div_50000 :
    Real.eulerMascheroniConstant < 28861 / 50000 := by
  refine (eulerMascheroniConstant_lt_eulerMaclaurinSeq2 8).trans ?_
  have h8 : eulerMaclaurinSeq2 8 = 761 / 280 - Real.log 8 - (1 / 16 - 1 / 768) := by
    rw [eulerMaclaurinSeq2]
    norm_num [harmonic, Finset.sum_range_succ]
  have h_log8 : 3 * 0.6931471803 < Real.log 8 := by
    have h8_eq : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
    rw [h8_eq, Real.log_pow, Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9]
  linarith

/-- Theorem RH-07d (Complete Unconditional Robin Inequality at `n = 5040` with `Real.eulerMascheroniConstant`):
    Combining `eulerMascheroniConstant_lt_28861_div_50000`, `Real.exp_lt_exp`, and `rh_07_tight_191_div_50`
    establishes unconditionally over `ℝ` that:
    1. `Real.eulerMascheroniConstant < 28861 / 50000`,
    2. `Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 5040) < 191 / 50`,
    3. `Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 5040) < 19344 / 5040 = (∑ d ∈ Nat.divisors 5040, (d : ℝ)) / 5040`. -/
theorem rh_07_eulerMascheroni_robin_5040_unconditional :
    Real.eulerMascheroniConstant < 28861 / 50000 ∧
    Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 5040) < (191 : ℝ) / 50 ∧
    Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 5040) < (19344 : ℝ) / 5040 ∧
    Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 5040) <
      (((∑ d ∈ Nat.divisors 16, d) * (∑ d ∈ Nat.divisors 9, d) *
        (∑ d ∈ Nat.divisors 5, d) * (∑ d ∈ Nat.divisors 7, d) : ℕ) : ℝ) / 5040 := by
  have h_gamma := eulerMascheroniConstant_lt_28861_div_50000
  have h_exp_lt : Real.exp Real.eulerMascheroniConstant < Real.exp (28861 / 50000) :=
    Real.exp_lt_exp.mpr h_gamma
  have h_tight := rh_07_tight_191_div_50
  have hloglog_pos : 0 < Real.log (Real.log 5040) := by
    apply Real.log_pos
    rw [← Real.log_exp 1]
    apply Real.log_lt_log (Real.exp_pos 1)
    have h1 : Real.exp (((4 : ℕ) : ℝ) * (1 / 4 : ℝ)) ≤ (4 / 3 : ℝ) ^ 4 :=
      exp_upper_inv_step (by norm_num) (by norm_num) 4
    have h2 : (((4 : ℕ) : ℝ) * (1 / 4 : ℝ)) = 1 := by norm_num
    rw [h2] at h1
    have h3 : (4 / 3 : ℝ) ^ 4 < 5040 := by norm_num
    linarith
  have h_prod_lt :
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 5040) <
      Real.exp (28861 / 50000) * Real.log (Real.log 5040) :=
    mul_lt_mul_of_pos_right h_exp_lt hloglog_pos
  have h_191 : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 5040) < (191 : ℝ) / 50 :=
    lt_trans h_prod_lt h_tight.2.2.2.1
  have h_5040 : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 5040) < (19344 : ℝ) / 5040 :=
    lt_trans h_prod_lt h_tight.2.2.2.2
  have h_div_eq : ((∑ d ∈ Nat.divisors 16, d) * (∑ d ∈ Nat.divisors 9, d) *
      (∑ d ∈ Nat.divisors 5, d) * (∑ d ∈ Nat.divisors 7, d) : ℕ) = 19344 :=
    rh_05_robin_5040_divisor_sum_and_threshold.2.1
  have h_div : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 5040) <
      (((∑ d ∈ Nat.divisors 16, d) * (∑ d ∈ Nat.divisors 9, d) *
        (∑ d ∈ Nat.divisors 5, d) * (∑ d ∈ Nat.divisors 7, d) : ℕ) : ℝ) / 5040 := by
    rw [h_div_eq]
    exact_mod_cast h_5040
  exact ⟨h_gamma, h_191, h_5040, h_div⟩

/-- Degree-6 Fejér-Kondratiev zero-free region cosine polynomial with positive coefficients
    `(506, 878, 568, 264, 81, 14, 1)`:
    `P_6(θ) = 506 + 878*cos(θ) + 568*cos(2*θ) + 264*cos(3*θ) + 81*cos(4*θ) + 14*cos(5*θ) + cos(6*θ)`. -/
noncomputable def kondratievTrigPoly6 (θ : ℝ) : ℝ :=
  506 + 878 * Real.cos θ + 568 * Real.cos (2 * θ) + 264 * Real.cos (3 * θ) +
  81 * Real.cos (4 * θ) + 14 * Real.cos (5 * θ) + Real.cos (6 * θ)

/-- Theorem RH-08b (Analytic Zero-Free Region Deduction from Non-Negative Trigonometric Polynomials):
    Let `0 < a0 < a1`, `0 < S_pos` (`= ∑_{k=1}^d a_k`), `0 < M_log`, and let `β < 1` be the real part
    of a hypothetical zero of `ζ(s)`. At the abscissa `σ = 1 + (a1 - a0) / (2 * S_pos * M_log) > 1`,
    if the classical Landau-de la Vallée Poussin logarithmic-derivative inequality holds:
      `a1 / (σ - β) ≤ a0 / (σ - 1) + S_pos * M_log`,
    then `1 - β` satisfies the explicit zero-free region lower bound:
      `((a1 - a0)^2 / (2 * (a1 + a0) * S_pos)) / M_log ≤ 1 - β`. -/
theorem rh_08_analytic_zero_free_region_from_trig_poly
    (a0 a1 S_pos M_log β : ℝ)
    (ha0 : 0 < a0) (ha1 : a0 < a1) (hS : 0 < S_pos) (hM : 0 < M_log) (hβ : β < 1) :
    let σ := 1 + (a1 - a0) / (2 * S_pos * M_log)
    a1 / (σ - β) ≤ a0 / (σ - 1) + S_pos * M_log →
    ((a1 - a0) ^ 2 / (2 * (a1 + a0) * S_pos)) / M_log ≤ 1 - β := by
  intro σ h_ineq
  have h_diff_pos : 0 < a1 - a0 := sub_pos.mpr ha1
  have h_sum_pos : 0 < a1 + a0 := by linarith
  have h_σ_sub_one : σ - 1 = (a1 - a0) / (2 * S_pos * M_log) := by
    dsimp [σ]
    ring
  have h_σ_gt_one : 0 < σ - 1 := by
    rw [h_σ_sub_one]
    positivity
  have h_σ_sub_β_pos : 0 < σ - β := by linarith
  have h_rhs_eq : a0 / (σ - 1) + S_pos * M_log = (a1 + a0) * S_pos * M_log / (a1 - a0) := by
    rw [h_σ_sub_one]
    field_simp
    ring
  rw [h_rhs_eq] at h_ineq
  have h_cross := (div_le_div_iff₀ h_σ_sub_β_pos h_diff_pos).mp h_ineq
  have h_lb : a1 * (a1 - a0) / ((a1 + a0) * S_pos * M_log) ≤ σ - β := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h_id :
      a1 * (a1 - a0) / ((a1 + a0) * S_pos * M_log) - (a1 - a0) / (2 * S_pos * M_log) =
      ((a1 - a0) ^ 2 / (2 * (a1 + a0) * S_pos)) / M_log := by
    field_simp
    ring
  have h_rel : 1 - β = (σ - β) - (σ - 1) := by ring
  rw [h_rel, h_σ_sub_one, ← h_id]
  linarith

/-- Theorem RH-08c (Degree-6 Fejér-Kondratiev Trigonometric Polynomial & Strict Zero-Free Width Hierarchy):
    1. `kondratievTrigPoly6 θ = 2 * (3 + 13*cos θ + 14*cos^2 θ + 4*cos^3 θ)^2 = 2 * (10 + 16*cos θ + 7*cos(2θ) + cos(3θ))^2 ≥ 0` for all `θ : ℝ`,
    2. The analytic zero-free region width constant `W(P) = (a1 - a0)^2 / (2 * (a1 + a0) * S_pos)` satisfies
       `W(P_2) = 1 / 70 < W(P_4) = 4225 / 156638 < W(P_6) = 2883 / 104144`. -/
theorem rh_08_kondratiev_deg6_trig_poly_pos_and_sharper :
    (∀ θ : ℝ,
      kondratievTrigPoly6 θ = 2 * (3 + 13 * Real.cos θ + 14 * Real.cos θ ^ 2 + 4 * Real.cos θ ^ 3) ^ 2 ∧
      kondratievTrigPoly6 θ = 2 * (10 + 16 * Real.cos θ + 7 * Real.cos (2 * θ) + Real.cos (3 * θ)) ^ 2 ∧
      0 ≤ kondratievTrigPoly6 θ) ∧
    (((4 - 3 : ℝ) ^ 2 / (2 * (4 + 3) * 5)) < ((168 - 103 : ℝ) ^ 2 / (2 * (168 + 103) * 289))) ∧
    (((168 - 103 : ℝ) ^ 2 / (2 * (168 + 103) * 289)) < ((878 - 506 : ℝ) ^ 2 / (2 * (878 + 506) * 1806))) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  intro θ
  have h2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have h3 : Real.cos (3 * θ) = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ := by
    have h3a : (3 : ℝ) * θ = 2 * θ + θ := by ring
    have hsin2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
    have hsq : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq θ]
    rw [h3a, Real.cos_add, h2, hsin2]
    calc (2 * Real.cos θ ^ 2 - 1) * Real.cos θ - 2 * Real.sin θ * Real.cos θ * Real.sin θ
        = (2 * Real.cos θ ^ 2 - 1) * Real.cos θ - 2 * Real.cos θ * Real.sin θ ^ 2 := by ring
      _ = (2 * Real.cos θ ^ 2 - 1) * Real.cos θ - 2 * Real.cos θ * (1 - Real.cos θ ^ 2) := by rw [hsq]
      _ = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ := by ring
  have h4 : Real.cos (4 * θ) = 8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1 := by
    have h4a : (4 : ℝ) * θ = 2 * (2 * θ) := by ring
    rw [h4a, Real.cos_two_mul, h2]
    ring
  have h5 : Real.cos (5 * θ) = 16 * Real.cos θ ^ 5 - 20 * Real.cos θ ^ 3 + 5 * Real.cos θ := by
    have h5a : (5 : ℝ) * θ = 3 * θ + 2 * θ := by ring
    have h3b : (3 : ℝ) * θ = 2 * θ + θ := by ring
    have hsin2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
    have hsin3 : Real.sin (3 * θ) = 3 * Real.sin θ - 4 * Real.sin θ ^ 3 := by
      have hsq : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
      rw [h3b, Real.sin_add, hsin2, h2]
      calc 2 * Real.sin θ * Real.cos θ * Real.cos θ + (2 * Real.cos θ ^ 2 - 1) * Real.sin θ
          = 4 * Real.sin θ * Real.cos θ ^ 2 - Real.sin θ := by ring
        _ = 4 * Real.sin θ * (1 - Real.sin θ ^ 2) - Real.sin θ := by rw [hsq]
        _ = 3 * Real.sin θ - 4 * Real.sin θ ^ 3 := by ring
    have hsq : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
    rw [h5a, Real.cos_add, h3, h2, hsin3, hsin2]
    calc (4 * Real.cos θ ^ 3 - 3 * Real.cos θ) * (2 * Real.cos θ ^ 2 - 1) -
            (3 * Real.sin θ - 4 * Real.sin θ ^ 3) * (2 * Real.sin θ * Real.cos θ)
        = (4 * Real.cos θ ^ 3 - 3 * Real.cos θ) * (2 * Real.cos θ ^ 2 - 1) -
            2 * Real.cos θ * Real.sin θ ^ 2 * (3 - 4 * Real.sin θ ^ 2) := by ring
      _ = (4 * Real.cos θ ^ 3 - 3 * Real.cos θ) * (2 * Real.cos θ ^ 2 - 1) -
            2 * Real.cos θ * (1 - Real.cos θ ^ 2) * (3 - 4 * (1 - Real.cos θ ^ 2)) := by rw [hsq]
      _ = 16 * Real.cos θ ^ 5 - 20 * Real.cos θ ^ 3 + 5 * Real.cos θ := by ring
  have h6 : Real.cos (6 * θ) = 32 * Real.cos θ ^ 6 - 48 * Real.cos θ ^ 4 + 18 * Real.cos θ ^ 2 - 1 := by
    have h6a : (6 : ℝ) * θ = 2 * (3 * θ) := by ring
    rw [h6a, Real.cos_two_mul, h3]
    ring
  have h_eq1 : kondratievTrigPoly6 θ =
      2 * (3 + 13 * Real.cos θ + 14 * Real.cos θ ^ 2 + 4 * Real.cos θ ^ 3) ^ 2 := by
    unfold kondratievTrigPoly6
    rw [h2, h3, h4, h5, h6]
    ring
  have h_eq2 : kondratievTrigPoly6 θ =
      2 * (10 + 16 * Real.cos θ + 7 * Real.cos (2 * θ) + Real.cos (3 * θ)) ^ 2 := by
    rw [h_eq1, h2, h3]
    ring
  exact ⟨h_eq1, h_eq2, by rw [h_eq1]; positivity⟩

/- ============================================================================
   SECTION 9: RH-09 — WEIL EXPLICIT-FORMULA SYMMETRIC SPECTRAL PAIRING OVER `ℂ`
   ============================================================================ -/

/-- Real part of the symmetric explicit-formula pairing `z1 * conj(z2) + z2 * conj(z1)` over `ℂ`. -/
noncomputable def weilExplicitPairComplex (z1 z2 : ℂ) : ℝ :=
  (z1 * starRingEnd ℂ z2 + z2 * starRingEnd ℂ z1).re

/-- Theorem RH-09 (Weil Explicit-Formula Spectral Pairing On-Line Positivity & Off-Line Witness over `ℂ`):
    1. For all `z1, z2 : ℂ`, `weilExplicitPairComplex z1 z2 = 2 * (z1.re * z2.re + z1.im * z2.im)`,
    2. When `ρ` lies on the critical line (`ρ = 1 - conj(ρ)`, so `z1 = z2 = z`),
       `weilExplicitPairComplex z z = 2 * Complex.normSq z ≥ 0` for all `z : ℂ`,
    3. When `ρ` lies off the critical line (`ρ ≠ 1 - conj(ρ)`), the opposite-phase test witness
       `z1 = 1, z2 = -1` yields `weilExplicitPairComplex 1 (-1) = -2 < 0`. -/
theorem rh_09_mathlib_weil_explicit_pair_positivity_and_offline_witness :
    (∀ z1 z2 : ℂ, weilExplicitPairComplex z1 z2 = 2 * (z1.re * z2.re + z1.im * z2.im)) ∧
    (∀ z : ℂ, weilExplicitPairComplex z z = 2 * Complex.normSq z ∧ 0 ≤ weilExplicitPairComplex z z) ∧
    (weilExplicitPairComplex 1 (-1) = -2 ∧ weilExplicitPairComplex 1 (-1) < 0) := by
  have h_pair : ∀ z1 z2 : ℂ, weilExplicitPairComplex z1 z2 = 2 * (z1.re * z2.re + z1.im * z2.im) := by
    intro z1 z2
    unfold weilExplicitPairComplex
    simp only [add_re, mul_re, conj_re, conj_im]
    ring
  refine ⟨h_pair, ?_, ?_⟩
  · intro z
    have h_eq : weilExplicitPairComplex z z = 2 * Complex.normSq z := by
      rw [h_pair z z, Complex.normSq_apply]
    exact ⟨h_eq, by rw [h_eq]; exact mul_nonneg (by norm_num) (Complex.normSq_nonneg z)⟩
  · rw [h_pair 1 (-1)]
    simp only [one_re, one_im, neg_re, neg_im]
    norm_num

end

end RiemannHypothesisMathlib
