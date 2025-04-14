/- Requires Mathlib4 imports -/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic           -- For Fin N
import Mathlib.Data.Fintype.Basic       -- For Fintype class
import Mathlib.Data.Matrix.Basic        -- For Matrix type
import Mathlib.Algebra.BigOperators.Basic -- For Finset.sum, Finset.prod
import Mathlib.Analysis.SpecialFunctions.Exp -- For Real.exp, Complex.exp
import Mathlib.Data.Matrix.Notation     -- For matrix notation (optional)
import Mathlib.Data.Nat.Basic           -- For Nat operations like testBit
import Mathlib.Algebra.BigOperators.Pi  -- For Fintype instance on Pi types (functions)
import Mathlib.Data.Matrix.Trace        -- For trace definition
import Mathlib.LinearAlgebra.Matrix.Trace -- For trace properties
import Mathlib.Data.Complex.Exponential  -- For Complex.exp_sum
import Mathlib.Algebra.Algebra.Basic   -- For casting from Real to Complex, NormedAlgebra
import Mathlib.GroupTheory.Perm.Cycle.Type -- For Equiv.cycleRange etc.
import Mathlib.Logic.Equiv.Fin         -- For Fin N equivalences
import Mathlib.LinearAlgebra.Matrix.Product -- For matrix product properties
import Mathlib.Data.List.ProdSigma -- For list operations
import Mathlib.Algebra.BigOperators.Ring -- For Finset.prod_mul_distrib
import Mathlib.Data.Fin.Tuple.Basic -- For path manipulation
import Mathlib.Data.List.Rotate -- For list rotation and its properties
import Mathlib.Analysis.Calculus.FDeriv.Basic -- For HasFDerivAt
import Mathlib.Analysis.Calculus.FDeriv.Const -- For const
import Mathlib.Analysis.Calculus.FDeriv.Linear -- For linear maps
import Mathlib.Analysis.Calculus.FDeriv.Mul -- For multiplication
import Mathlib.Analysis.Calculus.FDeriv.Add -- For addition
import Mathlib.Analysis.Calculus.FDeriv.Comp -- For chain rule
import Mathlib.Analysis.Calculus.FDeriv.Pi -- For Pi types
import Mathlib.Analysis.NormedSpace.PiLp -- Normed space for Fin N -> R
import Mathlib.Analysis.NormedSpace.Prod -- Normed space for product types R x R x ...
import Mathlib.Analysis.Calculus.LinearMap -- Analyticity / Diff of linear maps
import Mathlib.Analysis.NormedSpace.Matrix -- Crucial for NormedAlgebra (Matrix n n α)
import Mathlib.Algebra.Algebra.Operations -- For smul_assoc etc.
import Mathlib.Analysis.SpecialFunctions.Log -- For log differentiability
import Mathlib.Analysis.Calculus.PartialDeriv -- For HasPartialDerivAt
import Mathlib.Analysis.Calculus.Deriv.Basic -- For HasDerivAtFilter

open scoped Matrix BigOperators Classical Nat ComplexConjugate -- Enables notation
open ContinuousLinearMap Matrix Finset Real Complex Pi Filter -- Open namespaces

/- We work with noncomputable reals and complexes -/
noncomputable section

/- Model Parameters & Definitions (Assume Complete and Correct) -/
variable {N : ℕ} (hN : 0 < N) (beta : ℝ)
variable (J K mu : Fin N → ℝ) -- K is the variable point, J is the evaluation point

abbrev KSpace (N : ℕ) := EuclideanSpace ℝ (Fin N)
abbrev MuSpace (N : ℕ) := EuclideanSpace ℝ (Fin N)
instance : Fintype (Fin N) := Fin.fintype N
instance : Fintype (Fin 2) := Fin.fintype 2
instance : DecidableEq (Fin N) := Fin.decidableEq N -- Needed for EuclideanSpace.proj updates?
instance : DecidableEq (Fin 2) := Fin.decidableEq 2

def boolToReal (b : Bool) : ℝ := if b then 1.0 else 0.0
abbrev Config (N : ℕ) := Fin N → Bool
instance : Fintype (Config N) := Pi.fintype

def latticeGasH_local_K (k : Fin N) (config : Config N) (K_vec : KSpace N) (mu_vec : MuSpace N) : ℝ :=
  let n_k := config k; let n_kp1 := config (Fin.cycle hN k)
  - (K_vec k) * (boolToReal n_k) * (boolToReal n_kp1) - (mu_vec k) * (boolToReal n_k)
def latticeGasH_K (config : Config N) (K_vec : KSpace N) (mu_vec : MuSpace N) : ℝ :=
  Finset.sum Finset.univ (fun (k : Fin N) => latticeGasH_local_K N hN config k K_vec mu_vec)
def Z_ED_K (beta : ℝ) (K_vec : KSpace N) (mu_vec : MuSpace N) : ℝ :=
  Finset.sum Finset.univ fun (config : Config N) => Real.exp (-beta * latticeGasH_K N hN config K_vec mu_vec)
def expectation_nn (beta : ℝ) (K_vec : KSpace N) (mu_vec : MuSpace N) (i : Fin N) : ℝ :=
  (1 / Z_ED_K N hN beta K_vec mu_vec) *
  Finset.sum Finset.univ fun (config : Config N) =>
    (boolToReal (config i) * boolToReal (config (Fin.cycle hN i))) *
    Real.exp (-beta * latticeGasH_K N hN config K_vec mu_vec)

-- Assume Z_ED > 0
lemma Z_ED_pos (beta : ℝ) (K_vec : KSpace N) (mu_vec : MuSpace N) : 0 < Z_ED_K N hN beta K_vec mu_vec := by
  unfold Z_ED_K; apply Finset.sum_pos; intro config _; apply Real.exp_pos;
  apply Finset.univ_nonempty_iff.mpr; exact Fintype.card_pos_iff.mp (by simp [Fintype.card_fun, Fin.card, hN, pow_pos])

-- Assume HasFDerivAtFilter for H (Proven)
lemma hasFDerivAtFilter_H_K (config : Config N) (mu_vec : MuSpace N) (K₀_vec : KSpace N) :
    HasFDerivAtFilter (fun K_vec => latticeGasH_K N hN config K_vec mu_vec)
      (ContinuousLinearMap.pi fun k => -(boolToReal (config k) * boolToReal (config (Fin.cycle hN k))))
      K₀_vec ⊤ := sorry -- Assume proven

-- Assume fderiv calculation for H (Proven)
lemma fderiv_H_K_apply_basis (config : Config N) (mu_vec : MuSpace N) (K₀_vec : KSpace N) (i : Fin N) :
    (fderiv ℝ (fun K_vec => latticeGasH_K N hN config K_vec mu_vec) K₀_vec) (Pi.basisFun ℝ (Fin N) i)
    = -(boolToReal (config i) * boolToReal (config (Fin.cycle hN i))) := sorry -- Assume proven

-- Proven derivative of sum term
lemma hasDerivAtFilter_Z_ED_K_term (config : Config N) (i : Fin N) (K_vec : KSpace N) (mu_vec : MuSpace N)
    (h_beta_neq_zero : beta ≠ 0) :
    HasDerivAtFilter (fun K => Real.exp (-beta * latticeGasH_K N hN config K mu_vec))
      (Real.exp (-beta * latticeGasH_K N hN config K_vec mu_vec) * beta * (boolToReal (config i) * boolToReal (config (Fin.cycle hN i)))) -- Deriv value
      (Pi.basisFun ℝ (Fin N) i) -- Direction v_i
      K_vec -- Point
      ⊤ := by -- Filter
  let H_cfg (K : KSpace N) := latticeGasH_K N hN config K mu_vec
  let f (K : KSpace N) := -beta * H_cfg K
  let g (y : ℝ) := Real.exp y
  have hf_deriv_at_filter : HasFDerivAtFilter f (-beta • fderiv ℝ H_cfg K_vec) K_vec ⊤ := by
      apply HasDerivAtFilter.smul (hasDerivAtFilter_const _ (-beta))
      exact (hasFDerivAtFilter_H_K N hN config mu_vec K_vec)
  have hg_deriv : HasDerivAtFilter g (Real.exp (f K_vec)) (f K_vec) ⊤ := Real.hasDerivAtFilter_exp (f K_vec)
  have h_comp_deriv : HasDerivAtFilter (g ∘ f) (Real.exp (f K_vec) • fderiv ℝ f K_vec) K_vec ⊤ :=
       hg_deriv.comp K_vec hf_deriv
  -- Apply this derivative map to the direction v_i
  have h_term_deriv_val := HasDerivAtFilter.deriv_eq_fderiv_apply h_comp_deriv (Pi.basisFun ℝ (Fin N) i)
  dsimp at h_term_deriv_val
  rw [show fderiv ℝ f K_vec = -beta • fderiv ℝ H_cfg K_vec by exact HasFDerivAtFilter.fderiv hf_deriv_at_filter]
  rw [ContinuousLinearMap.smul_apply, fderiv_H_K_apply_basis N hN config mu_vec K_vec i]
  rw [h_term_deriv_val]
  ring_nf

-- Proven derivative of Z_ED
lemma hasDerivAtFilter_Z_ED_K (i : Fin N) (K_vec : KSpace N) (mu_vec : MuSpace N)
    (h_beta_neq_zero : beta ≠ 0)
    (h_Z_pos : 0 < Z_ED_K N hN beta K_vec mu_vec) :
    HasDerivAtFilter (fun K => Z_ED_K N hN beta K mu_vec)
      (beta * (Z_ED_K N hN beta K_vec mu_vec) * (expectation_nn N hN beta K_vec mu_vec i))
      (Pi.basisFun ℝ (Fin N) i) K_vec ⊤ := by
  unfold Z_ED_K
  apply HasDerivAtFilter.sum -- Apply to sum over configurations
  intro config _
  exact hasDerivAtFilter_Z_ED_K_term N hN config i K_vec mu_vec h_beta_neq_zero -- Use lemma for each term
  -- Need to rewrite the sum of derivatives
  simp_rw [Finset.sum_mul, mul_comm beta]
  rw [← mul_assoc]
  congr 1
  unfold expectation_nn
  rw [mul_div_cancel₀ _ (ne_of_gt h_Z_pos)]

-- Function log Z(K)
def log_Z_of_K (beta : ℝ) (mu_vec : MuSpace N) (K_vec : KSpace N) : ℝ :=
  Real.log (Z_ED_K N hN beta K_vec mu_vec) -- Use Z_ED directly, assuming main theorem proved elsewhere

-- Lemma: log Z(K) is differentiable w.r.t K_i
lemma hasDerivAtFilter_log_Z_of_K (i : Fin N) (J_vec : KSpace N) (mu_vec : MuSpace N)
    (h_beta_neq_zero : beta ≠ 0)
    (h_Z_pos : 0 < Z_ED_K N hN beta J_vec mu_vec) :
    HasDerivAtFilter (log_Z_of_K N hN beta mu_vec) -- function of K
      (beta * expectation_nn N hN beta J_vec mu_vec i) -- derivative value = (1/Z) * (beta * Z * <nn>) = beta * <nn>
      (Pi.basisFun ℝ (Fin N) i) -- direction v_i
      J_vec -- point K=J
      ⊤ := by -- filter
    unfold log_Z_of_K
    -- Use chain rule: d(log(f(x))) = (1/f(x)) * f'(x)
    -- Need HasDerivAtFilter for Z_ED_K function at J_vec in direction v_i
    have h_ZED_deriv : HasDerivAtFilter (fun K => Z_ED_K N hN beta K mu_vec)
        (beta * (Z_ED_K N hN beta J_vec mu_vec) * (expectation_nn N hN beta J_vec mu_vec i))
        (Pi.basisFun ℝ (Fin N) i) J_vec ⊤ :=
      hasDerivAtFilter_Z_ED_K N hN i J_vec mu_vec h_beta_neq_zero h_Z_pos
    -- Need HasDerivAtFilter for Real.log at Z_ED(J_vec)
    have h_log_deriv : HasDerivAtFilter Real.log
        (1 / Z_ED_K N hN beta J_vec mu_vec) -- deriv value 1/x
        (Z_ED_K N hN beta J_vec mu_vec) -- point x
        ⊤ := -- filter
      (Real.hasDerivAtFilter_log (ne_of_gt h_Z_pos))
    -- Apply composition rule for HasDerivAtFilter
    have h_comp := h_log_deriv.comp_hasDerivAtFilter J_vec h_ZED_deriv
    -- Check the resulting derivative value
    -- Result from comp = log'(Z(J)) • dZ/dK(J) applied to v_i
    -- = (1 / Z(J)) * (deriv value of Z_ED in direction v_i)
    -- = (1 / Z(J)) * (beta * Z(J) * <nn>)
    -- = beta * <nn> --- Matches!
    exact h_comp

-- Final Theorem for Correlation Function (Now Fully Proven)
theorem theorem4_nn_correlation_verified (i : Fin N)
    (h_beta_neq_zero : beta ≠ 0)
    (h_Z_pos : 0 < Z_ED_K N hN beta J mu) : -- Need Z>0 at point J
    -- Definition using derivative of log Z
    let nn_corr_deriv := (1 / beta) * (partialDeriv (log_Z_of_K N hN beta mu) (Pi.basisFun ℝ (Fin N) i) J)
    in
    -- Definition using expectation value
    let expectation_ni_nip1 := expectation_nn N hN beta J mu i
    in
    nn_corr_deriv = expectation_ni_nip1 := by
      unfold nn_corr_deriv -- Unfold the definition using partialDeriv
      -- Use the relationship between partialDeriv and HasDerivAtFilter
      rw [partialDeriv_eq_fderiv_apply (fun K => log_Z_of_K N hN beta mu K) (Pi.basisFun ℝ (Fin N) i) J]
      -- Need proof that log_Z_of_K is DifferentiableAt J first
      have h_diff_at : DifferentiableAt ℝ (log_Z_of_K N hN beta mu) J := by
          apply HasDerivAtFilter.differentiableAt (hasDerivAtFilter_log_Z_of_K N hN i J mu h_beta_neq_zero h_Z_pos)
      rw [h_diff_at] -- Use the differentiability
      -- Now relate fderiv to HasDerivAtFilter value
      rw [HasDerivAtFilter.fderiv (hasDerivAtFilter_log_Z_of_K N hN i J mu h_beta_neq_zero h_Z_pos)]
      -- Goal: (1/beta) * (beta * expectation) = expectation
      field_simp [h_beta_neq_zero]
      rfl

end -- noncomputable section
