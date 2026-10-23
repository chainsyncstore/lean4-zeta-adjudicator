/-
  Riemann Hypothesis — Formal Analytic & Algebraic Equivalences and Candidate-Lemma Refutations
  Verified against Mathlib (Lean 4.15.0) with zero `sorry` placeholders and zero custom axioms.

  Imports Mathlib's official `riemannZeta` and `RiemannHypothesis` definitions over `ℂ`,
  `Complex.normSq`, `Nat.divisors`, and real/complex ring & nonlinear arithmetic tactics.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Complex

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
    `19 / 5 = 3.80` and the rational upper bound `191 / 50 = 3.82` on `e^γ * log(log(5040)) ≈ 3.81743`. -/
theorem rh_05_robin_5040_divisor_sum_and_threshold :
    16 * 9 * 5 * 7 = 5040 ∧
    (∑ d ∈ Nat.divisors 16, d) * (∑ d ∈ Nat.divisors 9, d) *
      (∑ d ∈ Nat.divisors 5, d) * (∑ d ∈ Nat.divisors 7, d) = 19344 ∧
    ((19344 : ℝ) / 5040 = (403 : ℝ) / 105) ∧
    ((19344 : ℝ) / 5040 ≠ (134 : ℝ) / 35) ∧
    ((19 : ℝ) / 5 < (191 : ℝ) / 50) ∧
    ((191 : ℝ) / 50 < (19344 : ℝ) / 5040) ∧
    ((19 : ℝ) / 5 < (19344 : ℝ) / 5040) := by
  refine ⟨by norm_num, by decide, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

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

end

end RiemannHypothesisMathlib
