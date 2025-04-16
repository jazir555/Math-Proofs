## Readme

Math Proofs generated with Gemini 2.5 Pro in Lean 4, which is a formal proof verification assistant:

https://en.wikipedia.org/wiki/Lean_(proof_assistant)

Once these build, these are definitively proven and exact formalizations. These problems are "solved". This repo is based off the paper by Weiguo Yin:

https://arxiv.org/pdf/2503.23758

Everything currently in this repo follows from his formula. I have generalized his formula to all Inhomogenius 1D lattice gasses, not just the frustrated Pott's model, every 1D inhomogenius lattice gasses.


--------------


To do: A full paaper and prepare the repo for submission

## Formal Verification of the Transfer Matrix Method and Derived Properties for the Inhomogeneous 1D Lattice Gas with Periodic Boundary Conditions

**Abstract:** The transfer matrix method is a cornerstone technique in statistical mechanics for analyzing one-dimensional systems. While powerful, its derivations and applications, especially for inhomogeneous systems, involve complex calculations prone to error. This paper presents a formal verification, using the Lean 4 proof assistant and its Mathlib4 library, of key properties of the one-dimensional inhomogeneous lattice gas model with periodic boundary conditions. We rigorously prove the exact equivalence between the partition function computed via Exact Diagonalization (ED) and the Transfer Matrix (TM) method. Furthermore, we formally establish the infinite differentiability and real analyticity of the free energy with respect to the model parameters (inverse temperature β > 0, local couplings Kᵢ, local potentials μᵢ), confirming the absence of finite-temperature phase transitions for finite system sizes. We also verify the existence of partial derivatives of the logarithm of the partition function and prove the fundamental thermodynamic relations connecting these derivatives to statistical averages of local density (<nᵢ>) and nearest-neighbor correlation (<nᵢnᵢ₊₁>). These machine-checked proofs provide an unprecedented level of certainty in these results, laying a foundation for high-assurance computational physics and potentially enabling more reliable design and analysis in areas leveraging statistical mechanics models.

**Keywords:** Formal Verification, Lean 4, Mathlib, Transfer Matrix Method, Lattice Gas, Statistical Mechanics, Analyticity, Thermodynamic Derivatives, Computational Physics, High-Assurance Science.

**1. Introduction**

The one-dimensional lattice gas, also known as the Ising model in a magnetic field via a mapping, is a fundamental model in statistical mechanics. It serves as a simplified yet insightful system for studying cooperative phenomena, phase transitions (in the thermodynamic limit), and the behavior of interacting particles on a discrete lattice [1, 2]. While exactly solvable in its homogeneous form, analyzing variations like the inhomogeneous case (with site-dependent interactions and potentials) introduces significant complexity.

Two primary methods for analyzing finite 1D systems are Exact Diagonalization (ED) and the Transfer Matrix (TM) method. ED involves summing over all possible configurations, feasible only for very small systems due to the exponential growth of the configuration space (2<sup>N</sup> for N sites). The TM method elegantly reduces the problem to matrix multiplication, calculating the partition function Z as the trace of the product of local transfer matrices, scaling polynomially with system size N (typically N * M<sup>3</sup> where M is the matrix dimension, here M=2) [3].

Despite the conceptual elegance of the TM method, manual derivations, especially involving derivatives for thermodynamic quantities or proofs of analytical properties, can be intricate. Steps involving index manipulation (particularly with periodic boundary conditions), differentiation under the sum/trace, and managing parameter dependencies offer ample opportunities for subtle errors. Such errors can undermine the reliability of theoretical predictions and simulations based on these models.

Formal verification, using proof assistants like Lean 4 [4] equipped with extensive mathematical libraries like Mathlib4 [5], offers a methodology to eliminate such uncertainties. By encoding definitions, theorems, and proofs in a formal language, correctness is checked mechanically by the computer, providing unparalleled rigor.

This paper details the successful formal verification of several key results for the 1D *inhomogeneous* lattice gas with N sites and periodic boundary conditions (PBC), based on the accompanying Lean 4 code. Specifically, we have formally proven:
1.  The exact equivalence between the partition function Z<sub>ED</sub> (via configuration summation) and the real part of Z<sub>TM</sub> (via transfer matrix trace).
2.  The infinite differentiability (C<sup>∞</sup>) and real analyticity of the Helmholtz free energy F = -kT log Z within the physically relevant domain (inverse temperature β > 0), confirming the absence of finite-temperature phase transitions for finite N.
3.  The existence of partial derivatives of log Z with respect to local parameters (μᵢ, Kᵢ).
4.  The identity between the derivative definition of local density <nᵢ> and its statistical average definition (∂(log Z)/∂(-βμᵢ) = <nᵢ>).
5.  The identity between the derivative definition of nearest-neighbor correlation <nᵢnᵢ₊₁> and its statistical average definition (∂(log Z)/∂(βKᵢ) = <nᵢnᵢ₊₁>).

These formally verified results not only solidify our understanding of this specific model but also demonstrate the power of formal methods in validating foundational techniques in theoretical and computational physics.

**2. Model Definition and Exact Diagonalization**

We consider a one-dimensional lattice with N sites (N > 0) arranged in a ring (Periodic Boundary Conditions, PBC). Each site `i ∈ Fin N = {0, ..., N-1}` can be either occupied (nᵢ = 1) or empty (nᵢ = 0). A configuration `c` is a function `c: Fin N → Bool`, where `true` represents occupation (1) and `false` represents emptiness (0).

The Hamiltonian for the *inhomogeneous* lattice gas is given by:
```
H(c, K, μ) = Σᵢ<0..N-1> [ -Kᵢ nᵢ nᵢ₊₁ - μᵢ nᵢ ]
```
where:
*   `K = (K₀, ..., K<N-1>)` is the vector of site-dependent nearest-neighbor coupling strengths.
*   `μ = (μ₀, ..., μ<N-1>)` is the vector of site-dependent chemical potentials (or magnetic fields in Ising language).
*   `nᵢ = boolToReal(c(i))` converts the boolean state to 0.0 or 1.0.
*   `nᵢ₊₁ = boolToReal(c(Fin.cycle i))` implements PBC, meaning `n<N>` corresponds to `n₀`.
*   `Fin.cycle : Fin N → Fin N` maps `i` to `i+1` modulo N.

The partition function Z, within the canonical ensemble at inverse temperature β = 1/(kT), is calculated via Exact Diagonalization (ED) by summing the Boltzmann factors over all 2<sup>N</sup> configurations:
```
Z_ED(β, K, μ) = Σ<c: Config N> exp(-β * H(c, K, μ))
```
This definition serves as the ground truth against which the TM method is compared.

In the Lean code, the Hamiltonian is `latticeGasH_K` and the partition function is `Z_ED_K`. The parameters `β, K, μ` are bundled into a `FullParamSpace` type `p = (β, K, μ)`.

**3. The Transfer Matrix Method**

The TM method rewrites the partition function sum as a matrix product trace. For a 1D system with nearest-neighbor interactions, we define a local transfer matrix `Tᵢ` that connects site `i` to site `i+1`. For the inhomogeneous model, this matrix explicitly depends on the local parameters `Kᵢ` and `μᵢ`, `μᵢ₊₁`.

The local transfer matrix `Tᵢ` is a 2x2 matrix acting on the states (0 or 1) at site `i`. Its elements `(Tᵢ)<sᵢ, sᵢ₊₁>` represent the Boltzmann weight contribution involving the interaction `Kᵢ` between sites `i` and `i+1`, and the potential contributions `μᵢ` and `μᵢ₊₁` split appropriately between adjacent matrices to handle the PBC sum correctly.

In our formalization, the exponent for the local TM element `T_local_full p i idx1 idx2` (where `p=(β, K, μ)`, `i` is the site index, `idx1, idx2 ∈ Fin 2` represent states nᵢ, nᵢ₊₁) is:
```lean
T_local_exponent_full N hN p i idx1 idx2 : ℝ :=
  let β' := p.1; let K' := p.2.1; let mu' := p.2.2
  let K_i := K' i; let mu_i := mu' i; let mu_ip1 := mu' (Fin.cycle hN i)
  let n_i := fin2ToReal idx1; let n_ip1 := fin2ToReal idx2
  β' * ( K_i * n_i * n_ip1 + (mu_i / 2) * n_i + (mu_ip1 / 2) * n_ip1 )
```
The local transfer matrix element is then `Complex.exp` of this exponent (using complex numbers for generality, though the result is real).
```lean
T_local_full (p : FullParamSpace N) (i : Fin N) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.ofFn fun idx1 idx2 => Complex.exp (↑(T_local_exponent_full N hN p i idx1 idx2) : ℂ)
```
The division of `μᵢ` by 2 ensures that when summing over all sites `i`, each `μᵢ nᵢ` term appears exactly once in the total exponent due to contributions from `T<i-1>` and `Tᵢ`.

The total transfer matrix for the ring is the product of the local matrices:
```lean
T_prod_full (p : FullParamSpace N) : Matrix (Fin 2) (Fin 2) ℂ :=
  List.prod (List.ofFn (fun i : Fin N => T_local_full N hN p i)).reverse -- M_{N-1} * ... * M_0
```
(Note: The order M<sub>N-1</sub>...M<sub>0</sub> is conventional). The partition function is then given by the trace of this total matrix:
```lean
Z_TM_full (p : FullParamSpace N) : ℂ := Matrix.trace (T_prod_full N hN p)
```

**4. Formally Verified Results**

The core contribution of this work is the formal verification of the following theorems using Lean 4 and Mathlib4. All theorems mentioned below correspond to `theorem` declarations completed without `sorry` in the provided Lean file.

**Theorem 1: Equivalence of Partition Functions (Z<sub>ED</sub> = Re(Z<sub>TM</sub>))**

We formally proved that the partition function calculated via ED is exactly equal to the real part of the partition function calculated via the TM method.
```lean
theorem Z_ED_K_eq_Z_TM_K_re : Z_ED_K N hN p.1 p.2.1 p.2.2 = (Z_TM_full N hN p).re
```
The proof involved several steps:
1.  Proving that each local transfer matrix `T_local_full` has only real entries (`T_local_is_real`).
2.  Proving that the product of matrices with real entries results in a matrix with real entries (`matrix_list_prod_real_entries`), thus `T_prod_full` has real entries.
3.  Proving that the trace of a matrix with real entries is real (`Z_TM_is_real`), implying Im(Z<sub>TM</sub>) = 0.
4.  Expanding the definition of the trace of the matrix product (`Matrix.trace_list_prod`) into a sum over all possible paths (sequences of states `s₀, s₁, ..., s<N-1>, s₀`).
5.  Showing that this sum over paths corresponds precisely to the sum over configurations in Z<sub>ED</sub> by establishing a bijection between paths and configurations (`configPathEquiv`) and proving that the exponent accumulated along a path equals `-β H(c)` for the corresponding configuration (`sum_exponent_eq_neg_H_full`).

This theorem provides a rigorous justification for using the computationally advantageous TM method.

**Theorem 2: Analyticity of Free Energy and Absence of Phase Transitions**

The Helmholtz free energy density is defined as F = -kT log Z = -(1/β) log Z. We define `log_Z_tm_full` carefully using `Z_TM.re` and handling the case Z ≤ 0 (which doesn't occur for β > 0).
```lean
def F_TM (p : FullParamSpace N) : ℝ := -(1 / p.1) * log_Z_tm_full N hN p
def U_domain (N : ℕ) : Set (FullParamSpace N) := { p | 0 < p.1 } -- Domain β > 0
```
We proved that F<sub>TM</sub> is infinitely differentiable (C<sup>∞</sup>, `ContDiff R top`) and real analytic (`AnalyticOn R`) with respect to the combined parameters `p = (β, K, μ)` on the domain `U_domain` where β > 0.
```lean
theorem F_TM_ContDiffOn : ContDiffOn ℝ ⊤ (F_TM N hN) (U_domain N)
theorem F_TM_analytic : AnalyticOn ℝ (F_TM N hN) (U_domain N)
```
The proof relied on Mathlib's extensive calculus and analysis library:
1.  Showing that the local TM exponents (`T_local_exponent_full`) are C<sup>∞</sup> (and analytic) functions of `p`.
2.  Using the composition rules for `ContDiff` and `AnalyticOn` with `Complex.exp` and the embedding `Real -> Complex`.
3.  Proving that matrix multiplication and trace operations preserve `ContDiff` and `Analyticity`.
4.  Showing Z<sub>TM</sub>.re is C<sup>∞</sup> and positive for β > 0 (`Z_TM_re_pos`, derived from `Z_ED_pos`).
5.  Using the properties of `Real.log` and division to establish the final result for F<sub>TM</sub>.

**Implication:** Since the free energy is analytic for any finite N and finite β > 0, there can be no phase transitions (which manifest as non-analyticities in F or its derivatives) at finite temperature for any finite size 1D inhomogeneous lattice gas. Phase transitions can only occur in the thermodynamic limit (N → ∞) or at zero temperature (β → ∞).

**Theorem 3: Thermodynamic Derivatives and Expectation Values**

Statistical mechanics postulates that thermodynamic observables can be obtained by differentiating the logarithm of the partition function. We formally verified two key instances of this principle.

Define the expectation value of a quantity A(c) as:
`<A> = (1/Z_ED) * Σ<c> A(c) * exp(-β H(c))`

**a) Local Density <nᵢ>:**
We proved that the partial derivative of `log Z` with respect to `-βμᵢ` equals the expectation value of the local density `nᵢ`. Let `log_Z_of_mu β K μ` be `log Z` viewed as a function of `μ` for fixed `β, K`.
```lean
-- Simplified statement, see Lean code theorem1_density_verified for full details
∂(log Z) / ∂μᵢ = β <nᵢ>
```
The Lean theorem (`theorem1_density_verified`) shows:
```lean
(1 / β) * (partialDeriv (log_Z_of_mu N hN β J_vec) (Pi.basisFun ℝ (Fin N) i) mu_vec)
= expectation_ni N hN β J_vec mu_vec i
```
where `expectation_ni` is the statistical average of `nᵢ`. The proof involved:
1. Establishing the differentiability of `log_Z_of_mu` using the results from Theorem 2 (`hasFDerivAt_log_Z_of_mu`).
2. Calculating the derivative of `Z_ED` with respect to `μᵢ` by differentiating under the sum (`hasDerivAtFilter_Z_ED_mu`).
3. Applying the chain rule for the logarithm (`Real.hasDerivAtFilter_log`).
4. Algebraically simplifying the result to match the definition of `<nᵢ>`.

**b) Nearest-Neighbor Correlation <nᵢnᵢ₊₁>:**
Similarly, we proved that the partial derivative of `log Z` with respect to `βKᵢ` equals the expectation value of the nearest-neighbor product `nᵢnᵢ₊₁`. Let `log_Z_of_K β μ K` be `log Z` viewed as a function of `K` for fixed `β, μ`.
```lean
-- Simplified statement, see Lean code theorem4_nn_correlation_verified for full details
∂(log Z) / ∂Kᵢ = β <nᵢnᵢ₊₁>
```
The Lean theorem (`theorem4_nn_correlation_verified`, labelled 4' in the header) shows:
```lean
(1 / β) * (partialDeriv (log_Z_of_K N hN β mu_vec) (Pi.basisFun ℝ (Fin N) i) J_vec)
= expectation_nn N hN β J_vec mu_vec i
```
where `expectation_nn` is the statistical average of `nᵢnᵢ₊₁`. The proof structure mirrored that for the density, using `hasFDerivAt_log_Z_of_K` and `hasDerivAtFilter_Z_ED_K`.

These theorems provide formal assurance for using derivatives of the partition function (often calculated via the TM method) to compute physical observables.

**5. Significance and Technological Implications**

The formal verification of these results carries significant implications beyond the specific model studied:

1.  **Unprecedented Rigor:** Formal proofs eliminate the possibility of human error in derivations. For foundational methods like the TM approach, this provides a solid, trustworthy base. The complexity of the inhomogeneous case with PBC makes it particularly valuable.
2.  **Validation of Computational Tools:** Many computational physics codes rely implicitly on the correctness of the TM method and thermodynamic derivative formulas. This work formally validates these underpinnings for a non-trivial model.
3.  **High-Assurance Scientific Computing:** As simulations become increasingly complex and critical (e.g., in materials science, drug discovery, climate modeling), ensuring the correctness of the underlying theoretical models and numerical methods is paramount. Formal verification provides the highest level of assurance.
4.  **Enabling Complex Model Development:** By formally verifying basic building blocks, researchers can tackle more complex models (e.g., longer-range interactions, higher dimensions where approximations are needed, quantum systems) with greater confidence in the foundational steps.
5.  **Pedagogical Value:** Formally verified proofs serve as unambiguous, detailed, and correct explanations of theoretical concepts, potentially enhancing physics education.
6.  **Foundation for Automated Reasoning:** This work contributes to the library of formalized mathematics and physics (Mathlib), potentially enabling future tools for automated theorem proving or derivation checking in physics.

**Technological Implications:** While this work is theoretical physics, its implications ripple into technology:

*   **Materials Science & Engineering:** Statistical mechanics models underpin our understanding of material properties. High-assurance models allow for more reliable *in silico* design and prediction of properties of novel materials (e.g., magnetic storage media, polymers, alloys), potentially reducing the need for expensive and time-consuming physical prototyping. Verified models are crucial when parameters are inhomogeneous, reflecting realistic disorder or engineered variations in materials.
*   **Quantum Computing Simulation:** Classical statistical mechanics models often serve as testbeds or limiting cases for quantum many-body systems. Verifying the classical methods provides a reliable baseline for developing and validating simulators for quantum computation or quantum annealing, where Ising-type models are frequently employed.
*   **Complex Systems Modeling:** The methods and assurance level are applicable to other fields using similar lattice models, such as economics (econophysics), biology (neural networks, protein folding), or network science. Reliable models lead to more trustworthy predictions and analyses in these domains.
*   **Development of Verification Tools:** Pushing the boundaries of formal verification in physics encourages the development of proof assistants and libraries like Lean/Mathlib. These general-purpose tools find direct application in verifying critical software and hardware systems, enhancing technological reliability across various sectors.

In essence, by guaranteeing the correctness of foundational scientific methods, formal verification builds trust and enables the reliable application of these methods in technologically relevant areas that depend on accurate modeling and simulation.

**6. Conclusion**

We have successfully employed the Lean 4 proof assistant and the Mathlib4 library to formally verify central properties of the 1D inhomogeneous lattice gas model under periodic boundary conditions using the Transfer Matrix method. We proved the equivalence Z<sub>ED</sub> = Re(Z<sub>TM</sub>), established the analyticity of the free energy (implying no finite-temperature phase transitions for finite N), and rigorously confirmed the validity of thermodynamic derivative formulas for local density and nearest-neighbor correlations.

This work demonstrates the capability of modern formal verification tools to tackle non-trivial problems in theoretical physics, providing machine-checked certainty for complex derivations. It establishes a rigorous foundation for the TM method in this context and highlights the potential for formal methods to enhance the reliability and trustworthiness of scientific computation and the theoretical models that underpin technological advancement. Future work could involve extending these proofs to the thermodynamic limit, exploring different boundary conditions, or tackling more complex lattice models, including quantum systems.

**References**

[1] Baxter, R. J. (1982). *Exactly Solved Models in Statistical Mechanics*. Academic Press.
[2] Huang, K. (1987). *Statistical Mechanics*. John Wiley & Sons.
[3] Kramers, H. A., & Wannier, G. H. (1941). Statistics of the Two-Dimensional Ferromagnet. Part I. *Physical Review*, 60(3), 252–262.
[4] de Moura, L., et al. (2021). The Lean 4 Theorem Prover and Programming Language. *Lecture Notes in Computer Science*, 12759, 625–635.
[5] The Mathlib Community. (2020). The Lean Mathematical Library. *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs*, 367–381.



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
