**Title:** Formal Verification of an Exact Transfer Matrix Solution for the Inhomogeneous 1D Lattice Gas with Periodic Boundary Conditions

**Abstract:**
We present a mathematically rigorous solution for the classical one-dimensional lattice gas model with nearest-neighbor interactions (`J`) and arbitrary site-dependent chemical potentials (`mu(i)`) under periodic boundary conditions (PBC). Utilizing the transfer matrix (TM) method with a standard symmetric energy decomposition, we derive the exact partition function `Z` for finite system size `N` via the trace of the total transfer matrix product, `Z = Tr(Product(T_local(i)))`. The primary contribution of this work is the **formal verification** of this method using the Lean 4 proof assistant. We successfully prove the theorem stating that the partition function calculated via the TM method is identical to that obtained from the fundamental definition via Exact Diagonalization (ED) (summing over all `2^N` states) for any `N > 0`, `beta`, `J`, and any potential profile `mu`. This formal proof guarantees the mathematical exactness of the TM formulation for this class of inhomogeneous 1D systems, providing a fully verified computational tool and a rigorous benchmark for studying inhomogeneity effects.

**1. Introduction**

One-dimensional (1D) systems in statistical mechanics, despite their simplicity compared to higher dimensions, exhibit rich physical phenomena and often serve as crucial testing grounds for theoretical concepts [1]. Models like the Ising model, Potts model, and lattice gases provide insights into phase transitions, critical phenomena, and the effects of interactions and external fields [2]. Furthermore, understanding systems with quenched disorder or specific patterns of inhomogeneity is vital in fields ranging from condensed matter physics (e.g., localization, transport in disordered wires) [3] to nanotechnology and biophysics [4].

While exact solutions are rare in higher dimensions, 1D systems with finite-range interactions are often amenable to exact treatment using the Transfer Matrix (TM) method, particularly under periodic boundary conditions (PBC) [1, 5]. The TM method cleverly maps the summation over all configurations in the partition function to the trace of a product of local matrices, transforming an exponentially complex problem into one that scales linearly with system size `N` (though polynomially with the local state space size).

Standard TM applications often focus on homogeneous systems. However, real-world systems almost invariably contain inhomogeneities, whether intrinsic (e.g., electronic density variations) or extrinsic (e.g., dopants, defects, applied potentials). Calculating the exact thermodynamic properties of such *inhomogeneous* 1D systems is therefore highly desirable, providing benchmarks for approximate methods and direct insights into the role of disorder or patterned potentials.

This paper focuses on the 1D interacting lattice gas model, a fundamental model where sites can be occupied or empty, with interactions between occupied neighbors and a site-dependent energy cost/gain for occupation (chemical potential `mu(i)`). We allow `mu(i)` to be completely arbitrary, representing any pattern of potential variation. We apply the standard symmetric TM method to this inhomogeneous system under PBC. While the applicability of TM to inhomogeneous 1D chains is known, rigorous verification, especially through formal methods, is less common. The main contribution of this work is the **formal proof**, carried out within the Lean 4 proof assistant [6] using the Mathlib4 library [7], demonstrating that the partition function `Z_TM` calculated via the trace of the TM product is *identical* to the partition function `Z_ED` obtained from the fundamental definition (sum over all states with explicitly calculated Hamiltonian energies). This formal verification eliminates any potential discrepancy beyond fundamental floating-point limits in numerical implementations and establishes the mathematical exactness of the applied TM formulation for this generalized inhomogeneous model.

**2. Model Definition: The Inhomogeneous 1D Lattice Gas**

We consider a one-dimensional lattice of `N` sites arranged in a ring (implying Periodic Boundary Conditions, PBC), indexed by `i ∈ {0, 1, ..., N-1}` represented formally by `Fin N`. We assume `N > 0`. Each site `i` can be either empty or occupied by a single particle. We represent the state of site `i` by `n_i`, where `n_i = 0` for empty and `n_i = 1` for occupied. A configuration of the system is given by the set `{n_0, n_1, ..., n_{N-1}}`.

The energy of a given configuration is defined by the Hamiltonian:
`H({n_i}) = -J * sum_{i=0}^{N-1} n_i * n_{i+1} - sum_{i=0}^{N-1} mu(i) * n_i` (Eq. 1)

Here:
*   `J` is the uniform nearest-neighbor interaction strength. If `J > 0`, occupied neighbors attract (lower energy); if `J < 0`, they repel.
*   `mu(i)` is the site-dependent chemical potential (or negative of the site energy). A larger `mu(i)` favors occupation of site `i`. This term allows for arbitrary inhomogeneity.
*   The index `i+1` is taken modulo `N` due to PBC. For formal representation, we use `Fin.cycle hN i` where `hN : 0 < N`.
*   We use internal representations where `n_i` corresponds to `boolToReal(config i)` in Lean.

The system is in thermal equilibrium at inverse temperature `beta = 1/(kT)`.

**3. Methodology**

**3.1. Exact Diagonalization (ED)**
The fundamental definition of the partition function `Z` is the sum of Boltzmann factors over all possible `2^N` configurations:
`Z_ED = sum_{{n_i}} exp(-beta * H({n_i}))` (Eq. 2)

In our formalization (`Z_ED` function in Lean), this corresponds to summing `Real.exp (-beta * latticeGasH config)` over all `config : Fin N → Bool`. This calculation is exact but computationally intractable for large `N` due to the exponential number of states.

**3.2. Transfer Matrix (TM) Method**
The TM method reformulates the partition function calculation. We define a local transfer matrix `T'(i)` associated with the link between site `i` and site `i+1`. The state space at each site is {empty, occupied}, represented by `Fin 2`. `T'(i)` is thus a 2x2 matrix. We employ the standard symmetric formulation.

The matrix element `T'_{s_i, s_{i+1}}(i)`, connecting state `s_i ∈ {0, 1}` at site `i` to state `s_{i+1} ∈ {0, 1}` at site `i+1`, is given by `exp(beta * Exponent(i, s_i, s_{i+1}))`, where:

`Exponent(i, s_i, s_{i+1}) = J * s_i * s_{i+1} ` (Full interaction term linking `i` and `i+1`)
`                         + (mu(i) / 2) * s_i ` (Half of potential term at `i`)
`                         + (mu(i+1) / 2) * s_{i+1}` (Half of potential term at `i+1`) (Eq. 3)

Here, `s_i`, `s_{i+1}` represent the occupation numbers (0 or 1), and `mu(i+1)` uses the PBC index `(i+1) mod N`. The `beta` factor is absorbed into the exponent definition. Note the signs correspond to `exp(-beta * EnergyPart)`.

The total transfer matrix for the ring is obtained by multiplying the local matrices in order:
`T_total = T'(N-1) * T'(N-2) * ... * T'(0)` (Eq. 4)

The partition function under PBC is then exactly given by the trace of this total matrix:
`Z_TM = Tr(T_total)` (Eq. 5)

**3.3. Formal Verification in Lean 4**
To rigorously establish the exactness of the TM method (Eq. 5) for the Hamiltonian (Eq. 1) with arbitrary `mu(i)`, we formalized both `Z_ED` and `Z_TM` in the Lean 4 proof assistant using the Mathlib4 library. The central goal was to formally prove the theorem:

**Theorem:** `Z_ED = Complex.re(Z_TM)`

The proof involved several key steps, all formally verified within Lean:
1.  **Realness of Z_TM:** We first proved that although `Z_TM` is defined as the trace of a complex matrix product, its imaginary part is always zero (`Z_TM_is_real` theorem). This relies on showing that each `T_local(i)` matrix has only real entries (cast to complex), and that the product and trace of such matrices remain real.
2.  **Hamiltonian-Exponent Equivalence:** We proved a crucial lemma (`sum_exponent_eq_neg_H`) demonstrating that the sum of the symmetric local exponents defined in Eq. 3 over all sites `i` for a given configuration is exactly equal to `-beta` times the total Hamiltonian energy `H` (Eq. 1) for that configuration. This confirms the energetic consistency between the TM setup and the original Hamiltonian.
3.  **Configuration-Path Bijection:** We formally defined the natural bijection (`configPathEquiv`) between lattice configurations (`Fin N → Bool`) and periodic paths (`Fin N → Fin 2`) used in the trace expansion.
4.  **Trace Identity:** We formally proved the standard identity relating the trace of the matrix product to the sum over all closed paths (`trace_prod_reverse_eq_sum_path'''`). This involved proving the cyclic property of the trace for list products (`trace_prod_reverse_eq_trace_prod`) and leveraging Mathlib's `Matrix.trace_list_prod` theorem.
5.  **Final Assembly:** Using the trace identity, properties of `Complex.exp`, the Hamiltonian-Exponent equivalence, and the configuration-path bijection (`Finset.sum_equiv`), we formally showed that the expression for `Z_TM` transforms exactly into the expression for `Z_ED`, thus proving the main theorem.

**4. Results**

The primary result is the **successful completion of the formal proof** in Lean 4, demonstrating unequivocally that `Z_ED N hN beta J mu = (Z_TM N hN beta J mu).re` holds true for all `N > 0`, any real `beta` and `J`, and any function `mu : Fin N → ℝ`. This constitutes a rigorous mathematical verification of the exactness of the standard symmetric Transfer Matrix method for this inhomogeneous 1D lattice gas model under PBC.

The Lean proof explicitly constructs the ED and TM calculations and formally connects them through mathematical identities and equivalences, leaving no logical gaps (no `sorry` placeholders remain in the final verified code). This goes beyond numerical checks, which can only test a finite number of cases and are subject to floating-point limitations.

(Optional: Briefly mention numerical agreement for N=2/4 from Python as illustration: "Numerical checks for small N, such as N=4 with J=1, beta=1, and uniform mu=-0.5, confirmed perfect agreement between `log(Z_ED) = 3.0976...` and `log(Z_TM.re) = 3.0976...` within machine precision, consistent with the formal proof.")

**5. Discussion and Conclusion**

We have successfully applied the Transfer Matrix method to the 1D interacting lattice gas with arbitrary site-dependent potentials `mu(i)` and Periodic Boundary Conditions. More significantly, we have provided a **complete formal verification** of this method's exactness using the Lean 4 proof assistant. By proving `Z_ED = Z_TM.re`, we have rigorously shown that the partition function calculated via the trace of the transfer matrix product is mathematically identical to the fundamental definition obtained by summing over all states.

The significance of this formal proof is multifold. It provides absolute confidence in the correctness of the TM method for this class of inhomogeneous systems, eliminating potential subtle errors in implementation or interpretation. It establishes the TM calculation as an exact computational tool, not an approximation, suitable for generating benchmark results against which other methods (e.g., Monte Carlo, mean-field theories applied to disordered systems) can be compared. While the 1D lattice gas is simpler than many frontier research models (like those for quantum systems or HTS), it captures the essential challenge of handling arbitrary inhomogeneity. The formal verification for this model demonstrates the power of combining exact methods with proof assistants to build reliable foundations for studying more complex scenarios.

The verified TM framework can now be confidently used for numerical studies exploring the impact of specific inhomogeneity patterns (periodic, localized defects, random, quasi-periodic) on the thermodynamic properties (density, correlations, susceptibility, specific heat – derivable from Z) of the 1D lattice gas.

In conclusion, by formally proving the equivalence of the Exact Diagonalization and symmetric Transfer Matrix descriptions for the inhomogeneous 1D lattice gas with PBC, we have established a mathematically guaranteed, exact computational method. This provides a rigorous foundation for studying the physics of inhomogeneity in 1D systems and serves as a testament to the power of formal verification in computational physics.

**References**
[1] Baxter, R. J. (1982). *Exactly Solved Models in Statistical Mechanics*. Academic Press.
[2] Wu, F. Y. (1982). The Potts model. *Reviews of Modern Physics, 54*(1), 235.
[3] Evers, F., & Mirlin, A. D. (2008). Anderson transitions. *Reviews of Modern Physics, 80*(4), 1355.
[4] Läuger, P. (1972). Carrier-mediated ion transport. *Science, 178*(4056), 24-30.
[5] Kramers, H. A., & Wannier, G. H. (1941). Statistics of the two-dimensional ferromagnet. Part I. *Physical Review, 60*(3), 252.
[6] de Moura, L., et al. (2021). The Lean 4 Theorem Prover and Programming Language. *arXiv preprint arXiv:2102.09909*.
[7] The Mathlib Community. (2020). The Lean Mathematical Library. *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs*.

---
