# lean4-zeta-adjudicator

[![Lean 4.15.0](https://img.shields.io/badge/Lean-v4.15.0-blue)](./lean/RiemannHypothesisMathlib.lean) [![Mathlib v4.15.0](https://img.shields.io/badge/Mathlib-v4.15.0-purple)](./lean/RiemannHypothesisMathlib.lean) [![Zero Sorrys](https://img.shields.io/badge/sorry-0-brightgreen)](./lean/RiemannHypothesisMathlib.lean) [![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

This repository provides machine-checked **Lean 4.15.0** formalizations of symmetric zero configurations, conformal unit-disk margins, and analytic counterexamples to symmetry-only shortcut lemmas in two complementary layers alongside a standalone **LaTeX** manuscript ([`latex/riemann_hypothesis_adjudication.tex`](./latex/riemann_hypothesis_adjudication.tex)):

1. **Analytic `Mathlib` v4.15.0 Formalization over $\mathbb{C}$ and $\mathbb{R}$** ([`lean/RiemannHypothesisMathlib.lean`](./lean/RiemannHypothesisMathlib.lean)):
   - Directly imports Mathlib's official `riemannZeta` and `RiemannHypothesis` definitions (`Mathlib.NumberTheory.LSeries.RiemannZeta`), `Real.log`, `Real.exp`, `Real.cos`, `Complex.normSq`, and `Nat.divisors`.
   - Proves direct biconditional ($\leftrightarrow$) equivalences over $\mathbb{C}$ (`rh_01_mathlib_riemannHypothesis_iff_li_unit_disk` and `rh_02_mathlib_riemannHypothesis_iff_zero_orbit_variance`), complex-analytic counterexamples to symmetry-only candidate lemmas (`RH-03`..`RH-05`), single conjugate-pair Hadamard quadratic factor positivity (`RH-06`), **unconditional transcendental bounds** on $\log(5040)$, $\log\log(5040)$, and $e^\gamma \log\log(5040) < \frac{191}{50} < \frac{19344}{5040}$ inside the Lean 4 kernel (`RH-07`), and global non-negativity plus sharpened zero-free constant ratios for the degree-4 Fejér–Kondratiev cosine polynomial over $\mathbb{R}$ (`RH-08`).
2. **Zero-Dependency Core Lean 4 Formalization** ([`lean/RiemannHypothesisAdjudication.lean`](./lean/RiemannHypothesisAdjudication.lean)):
   - Verified in $< 2$ seconds using only the Lean 4 standard prelude (`Int` / `omega` / `decide`) without downloading Mathlib.

---

## Mathematical Overview (`RH-01` through `RH-08`)

### 1. Unconditional Structural Equivalences, Transcendental Bounds & Positivity Reductions (`RH-01`, `RH-02`, `RH-06`, `RH-07`, `RH-08` — PROVEN)
- **`RH-01` (Li–Bombieri Conformal Unit-Disk Equivalence over $\mathbb{C}$ & Mathlib `riemannZeta` Bridge)**:
  Defines `liNormMargin (ρ : ℂ) : ℝ := Complex.normSq ρ - Complex.normSq (ρ - 1)`. Proves that $\operatorname{Im}(\rho)$ cancels identically (`liNormMargin ρ = 2 * ρ.re - 1`), establishes exact antisymmetry `liNormMargin ρ + liNormMargin (1 - star ρ) = 0` and the Sum-of-Squares identity `liNormMargin ρ * (-liNormMargin (1 - star ρ)) = (2 * ρ.re - 1)^2 ≥ 0`, and proves the direct biconditional equivalence with Mathlib's `RiemannHypothesis` predicate:
  ```lean
  theorem rh_01_mathlib_riemannHypothesis_iff_li_unit_disk :
      RiemannHypothesis ↔
        ∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
          (0 ≤ liNormMargin s ∧ 0 ≤ liNormMargin (1 - star s))
  ```
- **`RH-02` (Completed $\xi(s)$ 4-Fold Zero Orbit Variance Collapse over $\mathbb{C}$ & Mathlib `riemannZeta` Bridge)**:
  For the 4-element symmetry orbit $\{\rho, \bar{\rho}, 1-\rho, 1-\bar{\rho}\} \subset \mathbb{C}$, proves that the real-part sum is invariantly $2$ (`xiOrbitRealSum ρ = 2`), the horizontal variance from $\frac{1}{2}$ equals `(2 * ρ.re - 1)^2 ≥ 0`, and critical-line localization holds if and only if `xiOrbitVariance s = 0` for every non-trivial zero of `riemannZeta`.
- **`RH-06` (Single Conjugate-Pair Quadratic Factor Positivity over $\mathbb{C}$)**:
  For real $s \in \mathbb{R}$ and complex $\rho \in \mathbb{C}$, proves that the single conjugate-pair factor `hadamardConjugatePair s ρ := ((s : ℂ) - ρ) * ((s : ℂ) - star ρ)` has zero imaginary part and real part equal to `(s - ρ.re)^2 + ρ.im^2 ≥ 0` (strictly positive whenever `ρ.im ≠ 0`; extending factorwise positivity to global infinite products requires separate analytic convergence theorems).
- **`RH-07` (Unconditional Transcendental Bounds on `Real.log 5040`, `Real.log (Real.log 5040)`, and Robin's Threshold at $n = 5040$ over $\mathbb{R}$)**:
  Proves completely inside the Lean 4 kernel (using Mathlib's `Real.sum_le_exp_of_nonneg` and `Real.add_one_le_exp` without any external interval assumptions) that $\log(5040) < \frac{4263}{500} = 8.526$ (and $< \frac{427}{50} = 8.54$), $\log\log(5040) < \frac{42865}{20000} = 2.14325$ (and $< \frac{4292}{2000} = 2.146$), $\exp\!\left(\frac{28861}{50000}\right) < \frac{178225}{100000} = 1.78225$ (where $\frac{28861}{50000} = 0.57722 > \gamma_{\mathrm{EM}} \approx 0.5772156649$), and
  $$\exp\!\left(\frac{28861}{50000}\right)\log\log(5040) \;<\; \frac{191}{50} \;<\; \frac{403}{105} \;=\; \frac{19344}{5040},$$
  via `rh_07_unconditional_log_and_robin_5040_bounds` and `rh_07_tight_191_div_50`.
- **`RH-08` (Degree-4 Fejér–Kondratiev Trigonometric Polynomial Non-Negativity & Zero-Free Constant Improvement over $\mathbb{R}$)**:
  Defines `kondratievTrigPoly4 (θ : ℝ) : ℝ := 103 + 168 * Real.cos θ + 89 * Real.cos (2 * θ) + 28 * Real.cos (3 * θ) + 4 * Real.cos (4 * θ)` and proves via Chebyshev multiple-angle identities (`Real.cos_two_mul`, `Real.sin_two_mul`, `Real.sin_sq_add_cos_sq`) that for all $\theta \in \mathbb{R}$,
  $$P_4(\theta) \;=\; 2\bigl(5 + 7\cos\theta + 2\cos(2\theta)\bigr)^2 \;=\; 2\bigl(3 + 7\cos\theta + 4\cos^2\theta\bigr)^2 \;\ge\; 0,$$
  while strictly improving both the pole-to-zero ratio $\frac{c_0}{c_1 - c_0} = \frac{103}{65} < 3$ and total weight ratio $\frac{\sum_{k=0}^4 c_k}{c_1 - c_0} = \frac{392}{65} < 8$ of de la Vallée Poussin's classical $3 + 4\cos\theta + \cos(2\theta) = 2(1+\cos\theta)^2$.

### 2. Formal Counterexamples to Symmetry-Only Shortcut Lemmas (`RH-03`, `RH-04`, `RH-05` — REFUTED BY COUNTEREXAMPLE)
- **`RH-03` (Refutation of "Functional Equation $G(1-s)=G(s)$ + Critical-Line Realness Prevents Off-Line Zeros" over $\mathbb{C}$)**:
  Proves that `symmetricCounterexampleG (s : ℂ) : ℂ := 16 * s^2 - 16 * s + 3` satisfies `G(1 - s) = G(s)` for all $s \in \mathbb{C}$ and `Im(G(1/2 + t * I)) = 0` for all $t \in \mathbb{R}$, yet has an explicit off-critical-line zero at $s = \frac{3}{4} \in \mathbb{C}$ (`0 < Re(s) < 1`, `Re(s) ≠ 1/2`) and satisfies `Re(G(1/2)) = -1 < 0`.
- **`RH-04` (Refutation of Universal Positivity of $\operatorname{Re}(\rho^2 + (1-\bar{\rho})^2)$ over $\mathbb{C}$)**:
  Proves the exact complex expansion `Re(ρ^2 + (1 - star ρ)^2) = 2 * ρ.re^2 - 2 * ρ.re + 1 - 2 * ρ.im^2` and shows that at $\rho = \frac{1}{2} + i$ on the critical line, `symSquareRealPart (1/2 + I) = -3/2 < 0`.
- **`RH-05` (Necessity of the $n > 5040$ Threshold in Robin's Divisor-Sum Criterion via `Nat.divisors`)**:
  Using Mathlib's `Nat.divisors` on the prime-power factors of $5040 = 16 \cdot 9 \cdot 5 \cdot 7$, verifies $\sigma(5040) = 19344$, proves the exact reduced fraction `(19344 : ℝ) / 5040 = 403 / 105` (and `≠ 134 / 35`), proves `(19 : ℝ) / 5 < (191 : ℝ) / 50 ∧ (191 : ℝ) / 50 < (19344 : ℝ) / 5040`, and proves the conditional implication `∀ c_robin : ℝ, c_robin ≤ 191 / 50 → c_robin < 19344 / 5040` (whose hypothesis $e^{\gamma}\log\log 5040 < \frac{191}{50}$ is unconditionally discharged in Lean by `rh_07_tight_191_div_50`).

---

## Quickstart

### Option A: Verify the Full `Mathlib` Formalization (`lean/RiemannHypothesisMathlib.lean`)
```bash
lake exe cache get
lake env lean lean/RiemannHypothesisMathlib.lean
```

### Option B: Verify the Zero-Dependency Core Formalization (`lean/RiemannHypothesisAdjudication.lean`)
```bash
lean lean/RiemannHypothesisAdjudication.lean
```

### Compile the LaTeX Manuscript
```bash
pdflatex latex/riemann_hypothesis_adjudication.tex
```

---

## Summary Table

| ID | Formalized Statement / Candidate Shortcut Lemma | Verdict | Mathlib Theorem(s) (`RiemannHypothesisMathlib.lean`) | Core Theorem(s) (`RiemannHypothesisAdjudication.lean`) |
| :--- | :--- | :--- | :--- | :--- |
| `RH-01` | **Li–Bombieri Conformal Unit-Disk Equivalence** ($\leftrightarrow$ `RiemannHypothesis`) | **PROVEN** | `rh_01_liNormMargin_eq_two_re_sub_one`, `rh_01_liNormMargin_antisymm`, `rh_01_liNormMargin_product_sos`, `rh_01_unit_disk_iff_critical_line`, `rh_01_mathlib_riemannHypothesis_iff_li_unit_disk` | `rh_01_li_margins_antisymmetric`, `rh_01_both_in_unit_disk_forces_zero_margin`, `rh_01_li_bombieri_unit_disk_equivalence`, `rh_01_li_margin_product_sos` |
| `RH-02` | **Completed $\xi(s)$ 4-Fold Zero Orbit Variance Collapse** ($\leftrightarrow$ `RiemannHypothesis`) | **PROVEN** | `rh_02_xiOrbitRealSum_invariant`, `rh_02_xiOrbitVariance_sos_and_collapse`, `rh_02_mathlib_riemannHypothesis_iff_zero_orbit_variance` | `rh_02_xi_quadruple_real_sum_invariant`, `rh_02_xi_quadruple_critical_line_collapse` |
| `RH-03` | **Shortcut Lemma**: $G(1-s)=G(s)$ + realness on $\operatorname{Re}(s)=\frac{1}{2}$ prevents off-line zeros | **REFUTED** | `rh_03_functional_equation_and_real_critical_line_refuted` | `rh_03_functional_equation_alone_refuted` |
| `RH-04` | **Shortcut Lemma**: Universal non-negativity of $\operatorname{Re}(\rho^2 + (1-\bar{\rho})^2)$ | **REFUTED** | `rh_04_symSquareRealPart_expansion`, `rh_04_symSquareRealPart_refuted_on_critical_line` | `rh_04_symmetric_square_real_part_refuted` |
| `RH-05` | **Shortcut Lemma**: Unqualified Robin divisor-sum bound without $n > 5040$ ($\frac{19344}{5040}=\frac{403}{105}>\frac{191}{50}$) | **REFUTED** | `rh_05_robin_5040_divisor_sum_and_threshold` | `rh_05_robin_5040_threshold_necessity` |
| `RH-06` | **Conjugate-Pair Factor Positivity**: $((s-\rho)(s-\bar{\rho})) = (s-\operatorname{Re}\rho)^2 + (\operatorname{Im}\rho)^2 \ge 0$ | **PROVEN** | `rh_06_hadamardConjugatePair_real_and_pos` | `rh_06_hadamard_conjugate_pair_positivity`, `rh_06_hadamard_conjugate_pair_strictly_pos_of_imag_nz` |
| `RH-07` | **Unconditional Transcendental Robin Bound**: $e^{\gamma}\log\log 5040 < \frac{191}{50} < \frac{403}{105} = \frac{19344}{5040}$ over $\mathbb{R}$ | **PROVEN** | `rh_07_unconditional_log_and_robin_5040_bounds`, `rh_07_tight_191_div_50` | `rh_07_transcendental_bracket_rational_certificate` |
| `RH-08` | **Degree-4 Fejér–Kondratiev Cosine Polynomial**: $P_4(\theta) = 2(3+7\cos\theta+4\cos^2\theta)^2 \ge 0$ & $\frac{103}{65} < 3$ | **PROVEN** | `rh_08_kondratiev_deg4_trig_poly_pos_and_sharper` | `rh_08_kondratiev_chebyshev_nonneg`, `rh_08_kondratiev_sharper_than_dlvp` |
