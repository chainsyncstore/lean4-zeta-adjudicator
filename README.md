# Riemann Hypothesis — Formal Equivalences & Candidate-Lemma Refutations in Lean 4 & LaTeX

[![Lean 4.15.0](https://img.shields.io/badge/Lean-v4.15.0-blue)](./lean/RiemannHypothesisAdjudication.lean) [![Zero Sorrys](https://img.shields.io/badge/sorry-0-brightgreen)](./lean/RiemannHypothesisAdjudication.lean) [![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

This repository contains machine-checked **Lean 4.15.0** formal proofs ([\`lean/RiemannHypothesisAdjudication.lean\`](./lean/RiemannHypothesisAdjudication.lean)) and a standalone **LaTeX** manuscript ([\`latex/riemann_hypothesis_adjudication.tex\`](./latex/riemann_hypothesis_adjudication.tex)) covering six formal propositions on the **Riemann Hypothesis (RH)**:

1. **Unconditional Structural Equivalences & Positivity Reductions (\`RH-01\`, \`RH-02\`, \`RH-06\` — PROVEN)**:
   - **\`RH-01\` (Li–Bombieri Conformal Unit-Disk Equivalence)**: Exact antisymmetry $D_1(\beta,\gamma) + D_2(\beta,\gamma) = 0$ and the Sum-of-Squares identity $D_1(\beta,\gamma)(-D_2(\beta,\gamma)) = (2\beta - 1)^2 \ge 0$, proving that a non-trivial zero $\rho$ and its reflection $1 - \bar{\rho}$ both lie in the Li unit disk $|1 - 1/\rho| \le 1$ if and only if $\operatorname{Re}(\rho) = \frac{1}{2}$.
   - **\`RH-02\` (Completed $\xi(s)$ 4-Fold Zero Orbit Variance Collapse)**: For the 4-element symmetry orbit $\{\beta \pm i\gamma, (1-\beta) \pm i\gamma\}$, the real-part sum is invariantly $2$ and the horizontal variance from $\frac{1}{2}$ is $(2\beta - 1)^2 \ge 0$, vanishing iff $\beta = \frac{1}{2}$.
   - **\`RH-06\` (Hadamard Conjugate-Pair Real-Axis Positivity)**: Every conjugate pair $\rho = \beta \pm i\gamma$ contributes a quadratic factor $H(s,\beta,\gamma) = (s - \beta)^2 + \gamma^2 \ge 0$ (strictly positive on $\mathbb{R}$ whenever $\gamma \ne 0$).
2. **Formal Refutations of Plausible Candidate RH Proof Lemmas (\`RH-03\`, \`RH-04\`, \`RH-05\` — REFUTED BY COUNTEREXAMPLE)**:
   - **\`RH-03\` (Refutation of "Functional Equation Alone Implies RH")**: Exhibits the algebraic Davenport–Heilbronn prototype $G(b) = 16b^2 - 16b + 3 = (4b-1)(4b-3)$, which satisfies $G(1-b) = G(b)$ identically yet vanishes off the critical line at $b = \frac{3}{4} \in (0,1)$ and takes a negative value $G(\frac{1}{2}) = -1 < 0$.
   - **\`RH-04\` (Refutation of Universal Positivity of $\operatorname{Re}(\rho^2 + (1-\bar{\rho})^2)$)**: Proves that while $J(\beta, 0) = \beta^2 + (1-\beta)^2 > 0$, at ordinate $\gamma = 1$ on the critical line $\beta = \frac{1}{2}$, $J(\frac{1}{2}, 1) = -\frac{3}{2} < 0$.
   - **\`RH-05\` (Necessity of the $n > 5040$ Threshold in Robin's Criterion)**: Proves via multiplicative prime-power factors that $\sigma(5040) = 31 \cdot 13 \cdot 6 \cdot 8 = 19344$, so $\frac{\sigma(5040)}{5040} = \frac{134}{35} > \frac{19}{5}$ with exact margin $19\cdot 5040 - 5\cdot 19344 = -960 < 0$.

---

## Quickstart (Verify with Lean 4)

No external dependencies or Mathlib downloads are required; the file uses only the Lean 4.15.0 standard prelude and core \`Int\` / \`omega\` / \`decide\` tactics:

\`\`\`bash
lean lean/RiemannHypothesisAdjudication.lean
\`\`\`

To compile the LaTeX manuscript:

\`\`\`bash
pdflatex latex/riemann_hypothesis_adjudication.tex
\`\`\`

---

## Summary Table

| ID | Mathematical Claim / Candidate Proof Lemma | Verdict | Lean 4 Theorem(s) |
| :--- | :--- | :--- | :--- |
| \`RH-01\` | **Li–Bombieri Conformal Unit-Disk Equivalence**: $D_1(\beta,\gamma)(-D_2(\beta,\gamma)) = (2\beta-1)^2 \ge 0$ | **PROVEN** | \`rh_01_li_margins_antisymmetric\`, \`rh_01_both_in_unit_disk_forces_zero_margin\`, \`rh_01_li_bombieri_unit_disk_equivalence\`, \`rh_01_li_margin_product_sos\` |
| \`RH-02\` | **Completed $\xi(s)$ 4-Fold Zero Orbit Variance Collapse**: $\sum (\operatorname{Re}\rho_k - \frac{1}{2})^2 = (2\beta-1)^2 \ge 0$ | **PROVEN** | \`rh_02_xi_quadruple_real_sum_invariant\`, \`rh_02_xi_quadruple_critical_line_collapse\` |
| \`RH-03\` | **Candidate Proof Lemma**: Functional equation $G(1-s)=G(s)$ alone prevents off-line zeros in $(0,1)$ | **REFUTED** | \`rh_03_functional_equation_alone_refuted\` |
| \`RH-04\` | **Candidate Proof Lemma**: Universal non-negativity of $\operatorname{Re}(\rho^2 + (1-\bar{\rho})^2)$ | **REFUTED** | \`rh_04_symmetric_square_real_part_refuted\` |
| \`RH-05\` | **Candidate Proof Lemma**: Unqualified Robin divisor-sum bound without $n > 5040$ | **REFUTED** | \`rh_05_robin_5040_threshold_necessity\` |
| \`RH-06\` | **Hadamard Conjugate-Pair Real-Axis Positivity**: $H(s,\beta,\gamma) = (s-\beta)^2 + \gamma^2 \ge 0$ | **PROVEN** | \`rh_06_hadamard_conjugate_pair_positivity\`, \`rh_06_hadamard_conjugate_pair_strictly_pos_of_imag_nz\` |
