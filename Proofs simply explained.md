**1. Equivalence of Partition Functions (Z_ED = Z_TM.re)**

**Proof:**

- **Exact Diagonalization (ED):** The partition function \( Z_{\text{ED}} \) is defined as the sum over all possible configurations \( \{n_i\} \):
  \[
  Z_{\text{ED}} = \sum_{\{n_i\}} \exp\left(-\beta H(\{n_i\})\right)
  \]
  where \( H(\{n_i\}) = -\sum_{i=1}^{N} K_i n_i n_{i+1} - \sum_{i=1}^{N} \mu_i n_i \), with \( n_{N+1} \equiv n_1 \) due to periodic boundary conditions.

- **Transfer Matrix (TM) Method:** The transfer matrix \( T_i \) for site \( i \) has elements:
  \[
  T_i(n_i, n_{i+1}) = \exp\left(\beta \left(K_i n_i n_{i+1} + \frac{\mu_i}{2} n_i + \frac{\mu_{i+1}}{2} n_{i+1}\right)\right)
  \]
  The partition function \( Z_{\text{TM}} \) is the trace of the product of these matrices:
  \[
  Z_{\text{TM}} = \text{Tr}\left(T_1 T_2 \cdots T_N\right)
  \]

- **Equivalence:** Since each matrix entry \( T_i(n_i, n_{i+1}) \) corresponds to the Boltzmann weight for the interaction between sites \( i \) and \( i+1 \), the product of matrices effectively sums over all configurations, with the trace enforcing periodic boundary conditions. Therefore:
  \[
  Z_{\text{ED}} = \text{Re}(Z_{\text{TM}})
  \]
  This holds because all entries of the transfer matrices are real and positive, ensuring \( Z_{\text{TM}} \) is real and positive, hence \( \text{Re}(Z_{\text{TM}}) = Z_{\text{TM}} \).

**2. Analyticity of the Free Energy (F_TM)**

**Proof:**

- **Free Energy Definition:**
  \[
  F_{\text{TM}} = -\frac{1}{\beta} \ln Z_{\text{TM}}
  \]

- **Analyticity of \( Z_{\text{TM}} \):** The transfer matrix entries are analytic functions of \( \beta \), \( K_i \), and \( \mu_i \) for \( \beta > 0 \). The product and trace operations preserve analyticity. Therefore, \( Z_{\text{TM}} \) is analytic in these parameters.

- **Logarithm and Analyticity:** The logarithm \( \ln Z_{\text{TM}} \) is analytic where \( Z_{\text{TM}} \neq 0 \). Since \( Z_{\text{TM}} > 0 \) for \( \beta > 0 \), \( \ln Z_{\text{TM}} \) is analytic in \( \beta \), \( K_i \), and \( \mu_i \).

- **Conclusion:** \( F_{\text{TM}} \) is analytic for \( \beta > 0 \), implying no finite-temperature phase transitions (singularities) in the free energy for finite \( N \).

**3. Existence of Partial Derivatives of \( \ln Z \)**

**Proof:**

- **Differentiability:** Since \( Z_{\text{TM}} \) is analytic, \( \ln Z_{\text{TM}} \) is differentiable to all orders with respect to \( \mu_i \) and \( K_i \).

- **Partial Derivatives:** The partial derivatives \( \frac{\partial \ln Z}{\partial \mu_i} \) and \( \frac{\partial \ln Z}{\partial K_i} \) exist and are continuous, given by:
  \[
  \frac{\partial \ln Z}{\partial \mu_i} = \frac{1}{Z} \frac{\partial Z}{\partial \mu_i} = \langle n_i \rangle
  \]
  \[
  \frac{\partial \ln Z}{\partial K_i} = \frac{1}{Z} \frac{\partial Z}{\partial K_i} = \langle n_i n_{i+1} \rangle
  \]
  where the averages are taken with respect to the Boltzmann distribution.

**4. Equality of Derivatives and Statistical Averages**

**Proof:**

- **Local Density \( \langle n_i \rangle \):**
  \[
  \langle n_i \rangle = \frac{\partial \ln Z}{\partial (\beta \mu_i)} = \frac{1}{\beta} \frac{\partial \ln Z}{\partial \mu_i}
  \]
  This follows directly from differentiating the partition function with respect to \( \mu_i \), which inserts \( n_i \) into the expectation value.

- **Nearest-Neighbor Correlation \( \langle n_i n_{i+1} \rangle \):**
  \[
  \langle n_i n_{i+1} \rangle = \frac{\partial \ln Z}{\partial (\beta K_i)} = \frac{1}{\beta} \frac{\partial \ln Z}{\partial K_i}
  \]
  Similarly, differentiating with respect to \( K_i \) inserts \( n_i n_{i+1} \) into the expectation value.
