# Lean Formalization of Generalization Error Bound by Rademacher Complexity
[![arXiv](https://img.shields.io/badge/arXiv-xxxx.xxxxx-b31b1b.svg)](https://arxiv.org/abs/xxxx.xxxxx)

## How to Run
- Open a terminal. Run the following commands.
  ```bash
  git clone https://github.com/[anonymous]
  cd lean-rademacher

  # get Mathlib4 cache 
  lake exe cache get
  ```
- Launch VS code,
- open the folder ```lean-rademacher```,
- select the file ```FoML/Main.lean```, and
- push ```Restart File``` button to rebuild the project.

## Contents (selected)
Key theorems (resp. definitions) are gathered in `Main.lean` (resp. `Defs.lean`), e.g.
- `FoML.Main.uniform_deviation_tail_bound_separable`
  - (Main Theorem) Generalization error bound using Rademacher complexity
- `FoML.Defs.empiricalRademacherComplexity` *et al.*
  - Definition(s) of Rademacher complexity 
- `FoML.Main.uniform_deviation_mcdiarmid_tail`
  - McDiarmid inequality (for deviations)
- `FoML.Main.linear_predictor_l2_bound`
  - Example: Generalization error bound for ridge regression (linear regression with $L^2$-regularization) 
- `FoML.Main.linear_predictor_l1_bound`
  - Example: Generalization error bound for lasso regression (linear regression with $L^1$-regularization)
- `FoML.Main.dudley_entropy_integral_bound`
  - Dudley's entropy integral bound for Rademacher complexity

### Future plans
Contributors are always welcome! (Contact: [Discord](https://discord.gg/[anonymous]))
- Examples of generalization error bounds such as
  - for RKHS
- Examples of *covering numbers* $N$ (of a function sets $H$ w.r.t. sup-norm or empirical-norm to instantiate Dudley's entropy bound) such as
  - the unit ball of Lipschitz-continuous functions on a compact set $K \subset \mathbb{R}^d$
  - neural networks with bounded weights
- Brushing-up key definitions/inequalies such as Rademacher complexity, Dudley's entropy bound, Azuma-Hoeffding, McDiarmid, ...
