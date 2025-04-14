# Model and Definitions

- **Parameter spaces** (`KSpace`, `MuSpace`, `FullParamSpace`) are defined using `EuclideanSpace` to support differentiation.
- **Helper functions** (`boolToReal`, `fin2ToBool`) correctly convert between boolean and real representations.
- **Hamiltonian** (`latticeGasH_local_K`, `latticeGasH_K`) accurately models local interactions with periodic boundary conditions.
- **Partition functions** (`Z_ED_K`, `Z_TM_full`) are implemented for both Exact Diagonalization and Transfer Matrix methods.

# Transfer Matrix Properties

- **Transfer matrix elements** (`T_local_full`) are defined using local Hamiltonian terms.
- **Product of transfer matrices** (`T_prod_full`) is computed in reverse order to ensure correct matrix multiplication.
- **Trace of the transfer matrix product** (`Z_TM_full`) correctly gives the partition function.

# Equivalence Theorem: `Z_ED = Z_TM.re`

- The **imaginary part** of the Transfer Matrix partition function is proven to be zero (`Z_TM_is_real`), ensuring it is real.
- The **main theorem** `Z_ED_K_eq_Z_TM_K_re` is rigorously proven by:
  - Equating sums over configurations to the trace of the transfer matrix product.
  - Leveraging the bijection between configurations and paths.

# Analyticity and Differentiability

- The **domain** `U_domain` restricts to positive beta values, ensuring the **free energy** (`F_TM`) is well-defined.
- **Theorems** `F_TM_ContDiffOn` and `F_TM_analytic` prove:
  - Infinite differentiability.
  - Analyticity.
  - These imply no finite-temperature phase transitions for finite systems.

# Derivative Relations

- **Expectation values**:
  - Local density: `expectation_ni`
  - Nearest-neighbor correlations: `expectation_nn`
- **Theorems**:
  - `theorem1_density_verified`
  - `theorem4_nn_correlation_verified`
  - These establish that derivatives of the log partition function match the expectation values, confirming key results in statistical mechanics.

# Code Structure and Rigor

- The code uses **Lean's type class system** and **Mathlib4's** library for rigorous mathematical foundations.
- **Noncomputable sections** are used appropriately where needed.
- All proofs are completed with **no `sorry` placeholders**, indicating full formal verification.
