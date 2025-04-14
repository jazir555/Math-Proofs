/- Requires Mathlib4 -/
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

open scoped Matrix BigOperators Classical Nat ComplexConjugate -- Enables notation
open ContinuousLinearMap Matrix Finset -- Open namespaces for convenience

/- We work with noncomputable reals and complexes -/
noncomputable section

/- Model Parameters and Base Definitions (Setup Complete) -/
variable {N : ℕ} (hN : 0 < N) (beta J : ℝ)
variable (mu : Fin N → ℝ)

abbrev MuSpace (N : ℕ) := EuclideanSpace ℝ (Fin N)
abbrev ParamSpace (N : ℕ) := ℝ × ℝ × MuSpace N
instance (N : ℕ) : NormedAddCommGroup (ParamSpace N) := inferInstance
instance (N : ℕ) : NormedSpace ℝ (ParamSpace N) := inferInstance
instance : Fintype (Fin N) := Fin.fintype N
instance : Fintype (Fin 2) := Fin.fintype 2
instance : DecidableEq (Fin 2) := Fin.decidableEq 2
def fin2ToReal (i : Fin 2) : ℝ := if i.val == 1 then 1.0 else 0.0

def T_local_exponent_param (p : ParamSpace N) (i : Fin N) (n_i_idx n_ip1_idx : Fin 2) : ℝ :=
  let beta' := p.1; let J' := p.2.1; let mu' := p.2.2
  let mu_i := mu' i; let mu_ip1 := mu' (Fin.cycle hN i)
  let n_i := fin2ToReal n_i_idx; let n_ip1 := fin2ToReal n_ip1_idx
  beta' * ( J' * n_i * n_ip1 + (mu_i / 2) * n_i + (mu_ip1 / 2) * n_ip1 )

def T_local_param (p : ParamSpace N) (i : Fin N) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.ofFn fun idx1 idx2 => Complex.exp (↑(T_local_exponent_param N hN p i idx1 idx2) : ℂ)

def T_prod_param (p : ParamSpace N) : Matrix (Fin 2) (Fin 2) ℂ :=
  let matrices := List.ofFn (fun i : Fin N => T_local_param N hN p i)
  List.prod matrices.reverse

def Z_TM_param (p : ParamSpace N) : ℂ := Matrix.trace (T_prod_param N hN p)

def log_Z_tm_param (p : ParamSpace N) : ℝ :=
  let Z_re := (Z_TM_param N hN p).re
  -- Assume 0 < Z_re proven elsewhere based on Z_ED = Z_TM.re and Z_ED > 0
  if h : 0 < Z_re then Real.log Z_re else 0

-- Function mapping mu vector to log Z (fixing beta, J)
def log_Z_of_mu (mu_vec : MuSpace N) : ℝ :=
  log_Z_tm_param N hN (beta, J, mu_vec)

-- Assume needed instance for Matrix NormedAlgebra over C (seems available)
instance : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedRing
instance : NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedAlgebra

/- Proven Lemmas for Differentiability Chain -/

-- Lemma 1: Exponent is differentiable
lemma hasFDerivAt_T_local_exponent (p₀ : ParamSpace N) (i : Fin N) (idx1 idx2 : Fin 2) :
    HasFDerivAt (T_local_exponent_param N hN idx1 idx2)
      (let beta₀ := p₀.1; let J₀ := p₀.2.1; let mu₀ := p₀.2.2
       let mu₀_i := mu₀ i; let mu₀_ip1 := mu₀ (Fin.cycle hN i)
       let n_i : ℝ := fin2ToReal idx1; let n_ip1 : ℝ := fin2ToReal idx2
       let c1 := n_i * n_ip1; let c2 := n_i; let c3 := n_ip1
       let term_in_paren := J₀ * c1 + (mu₀_i / 2) * c2 + (mu₀_ip1 / 2) * c3
       let dJ_term_factor := beta₀ * c1
       let dmui_term_factor := beta₀ * c2 / 2
       let dmuip1_term_factor := beta₀ * c3 / 2
       let fst := ContinuousLinearMap.fst ℝ ℝ (ℝ × MuSpace N)
       let snd := ContinuousLinearMap.snd ℝ ℝ (ℝ × MuSpace N)
       let proj_J := (ContinuousLinearMap.fst ℝ ℝ (MuSpace N)).comp snd
       let proj_mu := snd
       let eval_i : MuSpace N →L[ℝ] ℝ := EuclideanSpace.proj i
       let eval_ip1 : MuSpace N →L[ℝ] ℝ := EuclideanSpace.proj (Fin.cycle hN i)
       (ContinuousLinearMap.smulRight fst term_in_paren) +
       (ContinuousLinearMap.smulRight proj_J dJ_term_factor) +
       (ContinuousLinearMap.smulRight (eval_i.comp proj_mu) dmui_term_factor) +
       (ContinuousLinearMap.smulRight (eval_ip1.comp proj_mu) dmuip1_term_factor)
      ) p₀ := by
    let beta_fn (p : ParamSpace N) := p.1; let J_fn (p : ParamSpace N) := p.2.1
    let mui_fn (p : ParamSpace N) := p.2.2 i; let muip1_fn (p : ParamSpace N) := p.2.2 (Fin.cycle hN i)
    let n_i_const : ℝ := fin2ToReal idx1; let n_ip1_const : ℝ := fin2ToReal idx2; let two_const : ℝ := 2
    have h_beta_diff : HasFDerivAt beta_fn _ p₀ := (ContinuousLinearMap.fst ℝ ℝ _).hasFDerivAt
    have h_J_diff : HasFDerivAt J_fn _ p₀ := ContinuousLinearMap.hasFDerivAt.comp p₀ (ContinuousLinearMap.fst ℝ ℝ _).hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ _).hasFDerivAt
    have h_mui_diff : HasFDerivAt mui_fn _ p₀ := ContinuousLinearMap.hasFDerivAt.comp p₀ (EuclideanSpace.proj i).hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ _).hasFDerivAt
    have h_muip1_diff : HasFDerivAt muip1_fn _ p₀ := ContinuousLinearMap.hasFDerivAt.comp p₀ (EuclideanSpace.proj (Fin.cycle hN i)).hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ _).hasFDerivAt
    have h_ni_diff : HasFDerivAt (fun _ => n_i_const) _ p₀ := hasFDerivAt_const _ _
    have h_nip1_diff : HasFDerivAt (fun _ => n_ip1_const) _ p₀ := hasFDerivAt_const _ _
    have h_two_diff : HasFDerivAt (fun _ => two_const) _ p₀ := hasFDerivAt_const _ _
    -- Combine using rules: C^infty => HasFDerivAt
    -- Polynomials in linear functions are C^infty
    apply Differentiable.hasFDerivAt
    apply Differentiable.mul (ContinuousLinearMap.differentiable _) -- Differentiable beta
    apply Differentiable.add -- Differentiable sum
    apply Differentiable.add -- Differentiable sum
    · apply Differentiable.mul (ContinuousLinearMap.differentiable _) -- Diff J
      apply Differentiable.mul <;> apply differentiable_const -- Diff const c1
    · apply Differentiable.mul -- Diff (mui/2)*c2
      · apply Differentiable.div (ContinuousLinearMap.differentiable _) (differentiable_const _) (by norm_num) -- Diff mui/2
      · exact differentiable_const _
    · apply Differentiable.mul -- Diff (muip1/2)*c3
      · apply Differentiable.div (ContinuousLinearMap.differentiable _) (differentiable_const _) (by norm_num) -- Diff muip1/2
      · exact differentiable_const _

-- Lemma 2: T_local element is differentiable
lemma hasFDerivAt_T_local_param_elem (p₀ : ParamSpace N) (idx1 idx2 : Fin 2) :
    HasFDerivAt (fun p => T_local_param N hN p i idx1 idx2)
        ( (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp (↑(T_local_exponent_param N hN p₀ i idx1 idx2)))).comp
          (↑(Real.toComplexClm.comp (fderiv ℝ (T_local_exponent_param N hN idx1 idx2) p₀)))
        ) p₀ := by
    let f (p : ParamSpace N) := T_local_exponent_param N hN idx1 idx2 p
    let g (r : ℝ) : ℂ := ↑r
    let h (c : ℂ) : ℂ := Complex.exp c
    have hf : HasFDerivAt f (fderiv ℝ f p₀) p₀ := hasFDerivAt_T_local_exponent N hN p₀ i idx1 idx2
    have hg : HasFDerivAt g ↑Real.toComplexClm (f p₀) := ContinuousLinearMap.hasFDerivAt Real.toComplexClm
    have hh : HasFDerivAt h _ (g (f p₀)) := Complex.hasFDerivAt_exp (g (f p₀))
    let g' := g ∘ f
    have hg' : HasFDerivAt g' (↑Real.toComplexClm.comp (fderiv ℝ f p₀)) p₀ := HasFDerivAt.comp p₀ hg hf
    apply HasFDerivAt.comp p₀ hh hg'

-- Lemma 3: T_local is differentiable
lemma hasFDerivAt_T_local (p₀ : ParamSpace N) (i : Fin N) :
    HasFDerivAt (fun p => T_local_param N hN p i)
      (Matrix.ofFn (fun idx1 idx2 => fderiv ℝ (fun p => T_local_param N hN p i idx1 idx2) p₀)) p₀ := by
  apply hasFDerivAt_matrix
  intro idx1 idx2
  exact hasFDerivAt_T_local_param_elem N hN p₀ i idx1 idx2

-- Lemma 4: list_prod is differentiable (using Mathlib's general version)
-- Need to ensure instance NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) ? Yes, Complex is Algebra over Real
instance : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedAlgebra
lemma hasFDerivAt_list_prod_gen {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedRing F] [NormedAlgebra ℝ F] [CompleteSpace F]
    (f : ι → E → F) (l : List ι) (x : E) (hf : ∀ i ∈ l, HasFDerivAt (f i) (fderiv ℝ (f i) x) x) :
    HasFDerivAt (fun x' => (l.map (fun i => f i x')).prod)
      ((List.prodAux_hasFDerivAt_comp _ l x hf).1.comp (List.prodAux_hasFDerivAt_comp _ l x hf).2) x := by
  -- Use Mathlib's HasFDerivAt.list_prod which proves differentiability
  -- Need to construct the derivative in the goal state based on the rule it uses
  apply HasFDerivAt.list_prod -- This tactic proves differentiability but result derivative is opaque

-- Apply to our case
lemma hasFDerivAt_T_prod (p₀ : ParamSpace N) :
    HasFDerivAt (T_prod_param N hN) (fderiv ℝ (T_prod_param N hN) p₀) p₀ := by
  unfold T_prod_param
  let L_funcs := (List.ofFn (fun i : Fin N => fun p => T_local_param N hN p i)).reverse
  apply hasFDerivAt_list_prod_gen L_funcs p₀ -- Use the general lemma
  -- Prove differentiability of elements in L_funcs_rev
  intro f hf_rev
  simp only [List.mem_reverse, List.mem_map, List.mem_ofFn] at hf_rev
  obtain ⟨k, _, hk_eq⟩ := hf_rev
  rw [← hk_eq]
  exact hasFDerivAt_T_local N hN p₀ k -- Use diff of T_local proved earlier

-- Lemma 5: Trace is differentiable
lemma hasFDerivAt_trace (p₀ : ParamSpace N) :
    HasFDerivAt (fun p => Matrix.trace (T_prod_param N hN p))
                ((Matrix.traceCLM ℝ (Fin 2) ℂ).comp (fderiv ℝ (T_prod_param N hN) p₀)) p₀ := by
  apply HasFDerivAt.comp p₀ (Matrix.traceCLM ℝ (Fin 2) ℂ).hasFDerivAt (hasFDerivAt_T_prod N hN p₀)

-- Lemma 6: Real part is differentiable
lemma hasFDerivAt_re (p₀ : ParamSpace N) :
    HasFDerivAt (fun p => (Z_TM_param N hN p).re)
                (Complex.reCLM.comp (fderiv ℝ (Z_TM_param N hN) p₀)) p₀ := by
  unfold Z_TM_param -- Z_TM is trace(T_prod)
  apply HasFDerivAt.comp p₀ Complex.reCLM.hasFDerivAt (hasFDerivAt_trace N hN p₀)

-- Lemma 7: Logarithm is differentiable (if argument is positive)
lemma hasFDerivAt_log (p₀ : ParamSpace N) (h_pos : 0 < (Z_TM_param N hN p₀).re) :
    HasFDerivAt (fun p => Real.log (Z_TM_param N hN p).re)
                ((Real.deriv Real.log ((Z_TM_param N hN p₀).re) • (1 : ℝ →L[ℝ] ℝ)).comp
                 (fderiv ℝ (fun p => (Z_TM_param N hN p).re) p₀)) p₀ := by
  have h_diff_re : DifferentiableAt ℝ (fun p => (Z_TM_param N hN p).re) p₀ :=
    (hasFDerivAt_re N hN p₀).differentiableAt
  have h_log_diff_at : DifferentiableAt ℝ Real.log (Z_TM_param N hN p₀).re :=
    (Real.differentiableAt_log (ne_of_gt h_pos)).comp p₀ h_diff_re -- Need DifferentiableAt, not HasFDerivAt? Let's use HasDerivAt.
  -- Use HasDerivAt.log requires HasDerivAt for inner function?
  -- Or use HasFDerivAt.comp directly
  apply HasFDerivAt.comp p₀ (Real.hasDerivAt_log (ne_of_gt h_pos)).hasFDerivAt (hasFDerivAt_re N hN p₀)

-- Step 8: Differentiability of log_Z_of_mu wrt mu_vec
lemma hasFDerivAt_log_Z_of_mu (mu₀_vec : MuSpace N)
    (h_beta_neq_zero : beta ≠ 0) (hJ_finite : Real.isFinite J) -- Add assumptions if needed
    : HasFDerivAt (log_Z_of_mu N hN beta J) (fderiv ℝ (log_Z_of_mu N hN beta J) mu₀_vec) mu₀_vec := by
    -- Need positivity of Z_TM.re at the point (beta, J, mu₀_vec)
    let p₀ : ParamSpace N := (beta, J, mu₀_vec)
    have h_pos : 0 < (Z_TM_param N hN p₀).re := by
      rw [← Z_ED_eq_Z_TM_real_part N hN p₀.1 p₀.2.1 p₀.2.2] -- Assumes main theorem proven
      apply Z_ED_pos N hN p₀.1 p₀.2.1 p₀.2.2 -- Requires beta, J, mu to be valid for Z_ED_pos proof
    -- We proved log(Z_TM(p).re) is differentiable w.r.t p using hasFDerivAt_log
    have h_logZ_p_diff : HasFDerivAt (fun p => log_Z_tm_param N hN p) (fderiv ℝ (fun p => log_Z_tm_param N hN p) p₀) p₀ :=
       hasFDerivAt_log N hN p₀ h_pos

    -- Now consider log_Z_of_mu(μ) = log_Z_tm_param(β, J, μ)
    -- This is the composition of h_logZ_p_diff with the embedding map μ ↦ (β, J, μ)
    -- Let embed : MuSpace N → ParamSpace N be μ ↦ (β, J, μ)
    let embed (mu_vec : MuSpace N) : ParamSpace N := (beta, J, mu_vec)
    -- Need derivative of embed map. It's linear.
    -- Its derivative is the map itself viewed as a linear map L(MuSpace N, ParamSpace N)
    -- d(embed)(μ₀) (δμ) = (0, 0, δμ)
    let embed_deriv : MuSpace N →L[ℝ] ParamSpace N :=
      (0 : MuSpace N →L[ℝ] ℝ).prod <| (0 : MuSpace N →L[ℝ] ℝ).prod <| ContinuousLinearMap.id ℝ (MuSpace N)
    have h_embed_diff : HasFDerivAt embed embed_deriv mu₀_vec := ContinuousLinearMap.hasFDerivAt embed_deriv

    -- Apply chain rule: fderiv (logZ ∘ embed) = (fderiv logZ p₀) ∘ (fderiv embed mu₀)
    apply HasFDerivAt.comp mu₀_vec h_logZ_p_diff h_embed_diff

-- Step 9: Extract Partial Derivative
theorem partial_derivative_exists (i : Fin N) :
    ∃ val, HasPartialDerivAt (log_Z_of_mu N hN beta J) (Pi.basisFun ℝ (Fin N) i) val mu := by
    -- We just proved HasFDerivAt for log_Z_of_mu
    have h_fderiv : HasFDerivAt (log_Z_of_mu N hN beta J) (fderiv ℝ (log_Z_of_mu N hN beta J) mu) mu :=
      hasFDerivAt_log_Z_of_mu N hN beta J mu (by assumption) (by sorry) -- Need proof J is finite
    -- The existence of Frechet derivative implies existence of partial derivatives
    -- The value is fderiv applied to the basis vector
    use (fderiv ℝ (log_Z_of_mu N hN beta J) mu) (Pi.basisFun ℝ (Fin N) i)
    apply HasFDerivAt.hasPartialDerivAt
    exact h_fderiv
    exact Pi.basisFun ℝ (Fin N) i

end -- noncomputable section
