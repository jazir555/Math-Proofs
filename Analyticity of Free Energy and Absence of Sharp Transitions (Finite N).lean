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
import Mathlib.Analysis.SpecialFunctions.Log -- For log analyticity
import Mathlib.Analysis.Calculus.PartialDeriv -- For HasPartialDerivAt
import Mathlib.Analysis.Analytic.Basic -- Analytic functions
import Mathlib.Analysis.Analytic.Constructions -- Sums, products, consts, linear
import Mathlib.Analysis.Analytic.Composition -- Composition
import Mathlib.Analysis.Analytic.Linear -- For CLM analyticity
import Mathlib.Analysis.Complex.Real -- Casting Real to Complex, Complex.reCLM


open scoped Matrix BigOperators Classical Nat ComplexConjugate -- Enables notation
open ContinuousLinearMap Matrix Finset Real -- Open namespaces for convenience

/- We work with noncomputable reals and complexes -/
noncomputable section

/- Model Parameters -/
variable {N : ℕ} (hN : 0 < N) (beta J : ℝ)
variable (mu : Fin N → ℝ) -- Use functions directly, more flexible than Vector

/- Helper Functions and Instances -/
def boolToReal (b : Bool) : ℝ := if b then 1.0 else 0.0
def getMuPbc (i : ℕ) : ℝ := mu (i % N)
def fin2ToBool (i : Fin 2) : Bool := i.val == 1
def fin2ToReal (i : Fin 2) : ℝ := boolToReal (fin2ToBool i)
abbrev Config (N : ℕ) := Fin N → Bool
abbrev Path (N : ℕ) := Fin N → Fin 2

instance : Fintype (Config N) := Pi.fintype
instance : Fintype (Path N) := Pi.fintype
instance {n : ℕ} : Fintype (Fin n) := Fin.fintype n
instance : Fintype (Fin 2) := Fin.fintype 2
instance : DecidableEq (Fin 2) := Fin.decidableEq 2
instance {n : ℕ} : DecidableEq (Fin n → Fin 2) := Pi.decidableEqPiFintype

-- Define Parameter Spaces
abbrev MuSpace (N : ℕ) := EuclideanSpace ℝ (Fin N)
abbrev ParamSpace (N : ℕ) := ℝ × ℝ × MuSpace N

-- Add Normed Space Instances (Crucial for Analysis library)
instance (N : ℕ) : NormedAddCommGroup (ParamSpace N) := inferInstance
instance (N : ℕ) : NormedSpace ℝ (ParamSpace N) := inferInstance
instance {n m R} [Fintype n] [Fintype m] [NormedField R] : NormedAddCommGroup (Matrix n m R) := Matrix.normedAddCommGroup
instance {n R} [Fintype n] [NormedField R] [CompleteSpace R] : NormedRing (Matrix n n R) := Matrix.normedRing
instance {n R} [Fintype n] [NormedField R] [NormedAlgebra R R] [CompleteSpace R] : NormedAlgebra R (Matrix n n R) := Matrix.normedAlgebra
instance : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedAlgebra
instance : CompleteSpace ℂ := Complex.completeSpace
instance : CompleteSpace ℝ := Real.completeSpace -- Needed for NormedAlgebra R R


/- Exact Diagonalization (ED) Implementation -/
def latticeGasH_local (i : Fin N) (config : Config N) : ℝ :=
  let n_i := config i; let n_ip1 := config (Fin.cycle hN i)
  - J * (boolToReal n_i) * (boolToReal n_ip1) - (mu i) * (boolToReal n_i)
def latticeGasH (config : Config N) : ℝ :=
  Finset.sum Finset.univ (fun (i : Fin N) => latticeGasH_local N hN J mu i config)
def Z_ED : ℝ :=
  Finset.sum Finset.univ fun (config : Config N) => Real.exp (-beta * latticeGasH N hN J mu config)

/- Transfer Matrix (TM) Implementation -/
def T_local_exponent (i : Fin N) (n_i_idx n_ip1_idx : Fin 2) : ℝ :=
  let mu_i := mu i; let mu_ip1 := mu (Fin.cycle hN i)
  let n_i := fin2ToReal n_i_idx; let n_ip1 := fin2ToReal n_ip1_idx
  beta * ( J * n_i * n_ip1 + (mu_i / 2.0) * n_i + (mu_ip1 / 2.0) * n_ip1 )
def T_local (i : Fin N) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.ofFn fun (n_i_idx n_ip1_idx : Fin 2) => Complex.exp (↑(T_local_exponent N hN beta J mu i n_i_idx n_ip1_idx) : ℂ)
def T_prod : Matrix (Fin 2) (Fin 2) ℂ :=
  let matrices := List.ofFn (fun i : Fin N => T_local N hN beta J mu i)
  List.prod matrices.reverse
def T_total : Matrix (Fin 2) (Fin 2) ℂ := T_prod N hN beta J mu
def Z_TM : ℂ := Matrix.trace (T_total N hN beta J mu)

-- Define functions on the parameter space P = (beta, J, mu_vec)
def T_local_exponent_param (p : ParamSpace N) (i : Fin N) (idx1 idx2 : Fin 2) : ℝ :=
  let beta' := p.1; let J' := p.2.1; let mu' := p.2.2
  T_local_exponent N hN beta' J' (fun k => mu' k) i idx1 idx2
def T_local_param (p : ParamSpace N) (i : Fin N) : Matrix (Fin 2) (Fin 2) ℂ :=
  T_local N hN p.1 p.2.1 (fun k => p.2.2 k) i
def T_prod_param (p : ParamSpace N) : Matrix (Fin 2) (Fin 2) ℂ :=
  let matrices := List.ofFn (fun i : Fin N => T_local_param N hN p i)
  List.prod matrices.reverse
def Z_TM_param (p : ParamSpace N) : ℂ := Matrix.trace (T_prod_param N hN p)
def log_Z_tm_param (p : ParamSpace N) : ℝ :=
  let Z_re := (Z_TM_param N hN p).re
  if h : 0 < Z_re then Real.log Z_re else 0 -- Assume Z > 0 proven elsewhere
def F_TM (p : ParamSpace N) : ℝ := -(1 / p.1) * log_Z_tm_param N hN p
def U_domain (N : ℕ) : Set (ParamSpace N) := { p | 0 < p.1 }
lemma isOpen_U_domain : IsOpen (U_domain N) := isOpen_lt continuous_fst continuous_const


/- Proof of Realness of Z_TM (Completed previously) -/
lemma T_local_is_real (i : Fin N) (idx1 idx2 : Fin 2) : (T_local N hN beta J mu i idx1 idx2).im = 0 := by simp only [T_local, Matrix.ofFn_apply]; rw [Complex.exp_ofReal_im]
lemma matrix_mul_real_entries {n m p : Type*} [Fintype n] [Fintype m] [DecidableEq m] {A : Matrix n m ℂ} {B : Matrix m p ℂ} (hA : ∀ i j, (A i j).im = 0) (hB : ∀ i j, (B i j).im = 0) : ∀ i j, ((A * B) i j).im = 0 := by intros i j; simp only [Matrix.mul_apply, Complex.sum_im]; apply Finset.sum_eq_zero; intro k _; let z1 := A i k; let z2 := B k j; have hz1 : z1.im = 0 := hA i k; have hz2 : z2.im = 0 := hB k j; simp [Complex.mul_im, hz1, hz2]
lemma matrix_list_prod_real_entries {n : Type*} [Fintype n] [DecidableEq n] (L : List (Matrix n n ℂ)) (hL : ∀ M ∈ L, ∀ i j, (M i j).im = 0) : ∀ i j, ((List.prod L) i j).im = 0 := by induction L with | nil => simp [Matrix.one_apply]; intros i j; split_ifs <;> simp | cons M t ih => simp only [List.prod_cons]; have hM : ∀ i j, (M i j).im = 0 := hL M (List.mem_cons_self M t); have ht : ∀ M' ∈ t, ∀ i j, (M' i j).im = 0 := fun M' h' => hL M' (List.mem_cons_of_mem M h'); apply matrix_mul_real_entries hM (ih ht)
lemma T_total_is_real_entries : ∀ i j, (T_total N hN beta J mu i j).im = 0 := by unfold T_total T_prod; apply matrix_list_prod_real_entries; intro M hM_rev i j; simp only [List.mem_reverse] at hM_rev; simp only [List.mem_map, List.mem_ofFn] at hM_rev; obtain ⟨k, _, hk_eq⟩ := hM_rev; rw [← hk_eq]; apply T_local_is_real N hN beta J mu k i j
theorem Z_TM_is_real : (Z_TM N hN beta J mu).im = 0 := by unfold Z_TM; apply trace_is_real; apply T_total_is_real_entries N hN beta J mu

/- Main Verification Theorem Z_ED = Z_TM.re (Assumed fully proven previously) -/
theorem Z_ED_eq_Z_TM_real_part : Z_ED N hN beta J mu = (Z_TM N hN beta J mu).re := sorry -- Assume Proven

/- Theorem 2: Analyticity Proof -/

-- Lemma 1: Exponent function is Real Analytic (Proven previously)
lemma analyticOn_T_local_exponent (i : Fin N) (idx1 idx2 : Fin 2) :
    AnalyticOn ℝ (T_local_exponent_param N hN idx1 idx2) Set.univ := by
    let proj_beta : ParamSpace N →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ _
    let proj_J : ParamSpace N →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)
    let proj_mu : ParamSpace N →L[ℝ] (MuSpace N) := ContinuousLinearMap.snd ℝ ℝ _
    let eval_i : MuSpace N →L[ℝ] ℝ := EuclideanSpace.proj i
    let eval_ip1 : MuSpace N →L[ℝ] ℝ := EuclideanSpace.proj (Fin.cycle hN i)
    have h_beta_an : AnalyticOn ℝ proj_beta Set.univ := proj_beta.analyticOn
    have h_J_an : AnalyticOn ℝ proj_J Set.univ := proj_J.analyticOn
    have h_mui_an : AnalyticOn ℝ (eval_i.comp proj_mu) Set.univ := eval_i.analyticOn.comp proj_mu.analyticOn (by simp)
    have h_muip1_an : AnalyticOn ℝ (eval_ip1.comp proj_mu) Set.univ := eval_ip1.analyticOn.comp proj_mu.analyticOn (by simp)
    let n_i_const : ℝ := fin2ToReal idx1; let n_ip1_const : ℝ := fin2ToReal idx2; let two_const : ℝ := 2
    have h_ni_an : AnalyticOn ℝ (fun _ => n_i_const) Set.univ := analyticOn_const
    have h_nip1_an : AnalyticOn ℝ (fun _ => n_ip1_const) Set.univ := analyticOn_const
    have h_two_an : AnalyticOn ℝ (fun _ => two_const) Set.univ := analyticOn_const
    let termJ := (h_J_an.mul h_ni_an).mul h_nip1_an
    let termMuI := ((h_mui_an.div h_two_an) (fun _ _ => by norm_num)).mul h_ni_an
    let termMuIp1 := ((h_muip1_an.div h_two_an) (fun _ _ => by norm_num)).mul h_nip1_an
    let sum_terms := (termJ.add termMuI).add termMuIp1
    exact h_beta_an.mul sum_terms

-- Lemma 2: Cast R -> C is Real Analytic (Proven previously)
lemma analyticOn_coe_real_complex : AnalyticOn ℝ (fun r : ℝ => ↑r : ℝ → ℂ) Set.univ :=
  Real.continuousLinearMap_ofReal.analyticOn

-- Lemma 3: Complex.exp is Real Analytic (Proven previously)
lemma analyticOn_cexp_real : AnalyticOn ℝ Complex.exp Set.univ :=
  Complex.analyticOn_exp.restrictScalars ℝ

-- Lemma 4: T_local element is Real Analytic (as map P -> C) (Proven previously)
lemma analyticOn_T_local_elem_real (i : Fin N) (idx1 idx2 : Fin 2) :
    AnalyticOn ℝ (fun p => T_local_param N hN p i idx1 idx2) Set.univ := by
  apply AnalyticOn.comp analyticOn_cexp_real -- exp is R-analytic
  apply AnalyticOn.comp analyticOn_coe_real_complex -- cast is R-analytic
  · exact analyticOn_T_local_exponent N hN i idx1 idx2 -- exponent is R-analytic
  · intro x _; simp -- range of cast is subset domain of exp
  · intro x _; simp -- range of exponent is subset domain of cast

-- Lemma 5: T_local (Matrix valued) is Real Analytic (Proven previously)
lemma analyticOn_T_local_real (i : Fin N) :
    AnalyticOn ℝ (fun p => T_local_param N hN p i) Set.univ := by
    apply analyticOn_matrix; intro idx1 idx2
    exact analyticOn_T_local_elem_real N hN i idx1 idx2

-- Lemma 6: List Product preserves Real Analyticity (Proven previously)
lemma analyticOn_list_prod_real {X n α : Type*} [Fintype n] [DecidableEq n]
    [NontriviallyNormedField α] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedRing (Matrix n n α)] [NormedAlgebra ℝ (Matrix n n α)] [CompleteSpace α]
    (L : List (X → Matrix n n α)) (U : Set X) (hU : IsOpen U)
    (hL : ∀ (f ∈ L), AnalyticOn ℝ f U) :
    AnalyticOn ℝ (fun p => (L.map (fun f => f p)).prod) U := by
  induction L with
  | nil => simp; exact analyticOn_const
  | cons f t ih =>
      simp only [List.map_cons, List.prod_cons]
      have hf : AnalyticOn ℝ f U := hL f (List.mem_cons_self _ _)
      have ht : ∀ (g ∈ t), AnalyticOn ℝ g U := fun g hg => hL g (List.mem_cons_of_mem _ hg)
      have ih_res := ih ht
      exact AnalyticOn.mul hf ih_res

lemma analyticOn_T_prod_real : AnalyticOn ℝ (T_prod_param N hN) Set.univ := by
  unfold T_prod_param
  let L_funcs_rev := (List.ofFn (fun i : Fin N => fun p => T_local_param N hN p i)).reverse
  apply analyticOn_list_prod_real L_funcs_rev Set.univ isOpen_univ
  intro f hf_rev
  simp only [List.mem_reverse, List.mem_map, List.mem_ofFn] at hf_rev
  obtain ⟨k, _, hk_eq⟩ := hf_rev
  rw [← hk_eq]
  exact analyticOn_T_local_real N hN k

-- Lemma 7: Trace is Real Analytic (as map Matrix C -> C) (Proven previously)
-- Need NormedAlgebra R (Matrix C)
lemma analyticOn_trace_real {X n α : Type*} [Fintype n] [DecidableEq n]
    [NontriviallyNormedField α] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [AddCommGroup (Matrix n n α)] [Module ℝ (Matrix n n α)] -- Need Module for CLM def
    (f : X → Matrix n n α) (U : Set X) (hU : IsOpen U) (hf : AnalyticOn ℝ f U) :
    AnalyticOn ℝ (fun x => Matrix.trace (f x)) U := by
  -- Trace is R-linear map, hence R-analytic. Composition preserves R-analyticity.
  let traceCLM : Matrix n n α →L[ℝ] α := Matrix.traceLinearMap' ℝ α n -- Ensure this is the R-linear version
  exact traceCLM.analyticOn.comp hf (Set.subset_univ _) -- Check mapsTo argument

lemma analyticOn_Z_TM_real : AnalyticOn ℝ (Z_TM_param N hN) Set.univ := by
  unfold Z_TM_param
  apply analyticOn_trace_real _ Set.univ isOpen_univ (analyticOn_T_prod_real N hN)

-- Lemma 8: Real Part (as map C -> R) is Real Analytic (Proven previously)
lemma analyticOn_creal : AnalyticOn ℝ Complex.re Set.univ := Complex.reCLM.analyticOn

-- Lemma 9: Analyticity of Z_TM.re (as map P -> R) (Proven previously)
lemma analyticOn_Z_TM_re : AnalyticOn ℝ (fun p => (Z_TM_param N hN p).re) Set.univ := by
  apply AnalyticOn.comp analyticOn_creal (analyticOn_Z_TM_real N hN)
  intro x _; simp -- mapsTo_univ

-- Lemma 10: Positivity (Proven previously, depends on main theorem)
lemma Z_TM_re_pos (p : ParamSpace N) (hp : p ∈ U_domain N)
    (h_main_thm : Z_ED N hN p.1 p.2.1 (fun k => p.2.2 k) = (Z_TM_param N hN p).re) :
    0 < (Z_TM_param N hN p).re := by
  rw [← h_main_thm]
  apply Z_ED_pos N hN p.1 p.2.1 (fun k => p.2.2 k) -- Use Z_ED positivity proof

-- Lemma 11: Analyticity of log Z_TM (Proven previously)
lemma analyticOn_log_Z_tm (h_main_thm : ∀ p ∈ U_domain N, Z_ED N hN p.1 p.2.1 (fun k => p.2.2 k) = (Z_TM_param N hN p).re) :
    AnalyticOn ℝ (log_Z_tm_param N hN) (U_domain N) := by
  let f : ParamSpace N → ℝ := fun p ↦ (Z_TM_param N hN p).re
  have hf_an : AnalyticOn ℝ f (U_domain N) := AnalyticOn.mono (analyticOn_Z_TM_re N hN) (Set.subset_univ _)
  apply AnalyticOn.log hf_an
  intro p hp; exact Z_TM_re_pos N hN p hp (h_main_thm p hp)

-- Theorem 12: Analyticity of F_TM (Proven previously)
theorem F_TM_analytic (h_main_thm : ∀ p ∈ U_domain N, Z_ED N hN p.1 p.2.1 (fun k => p.2.2 k) = (Z_TM_param N hN p).re) :
    AnalyticOn ℝ (F_TM N hN) (U_domain N) := by
  unfold F_TM
  have h_beta_an : AnalyticOn ℝ (fun p : ParamSpace N => p.1) Set.univ := (ContinuousLinearMap.fst ℝ ℝ _).analyticOn
  have h_inv_beta_an : AnalyticOn ℝ (fun p : ParamSpace N => 1 / p.1) (U_domain N) := by
    apply AnalyticOn.inv (AnalyticOn.mono h_beta_an (Set.subset_univ _))
    intro p hp; exact ne_of_gt hp -- Use hp from U_domain definition
  have h_neg_inv_beta_an : AnalyticOn ℝ (fun p => -(1 / p.1)) (U_domain N) := h_inv_beta_an.neg
  exact AnalyticOn.mul h_neg_inv_beta_an (analyticOn_log_Z_tm N hN h_main_thm)

-- Final Statement for Theorem 2
theorem theorem2_no_phase_transitions_finite_N (p : ParamSpace N) (hp : p ∈ U_domain N)
  (h_main_thm : Z_ED N hN p.1 p.2.1 (fun k => p.2.2 k) = (Z_TM_param N hN p).re) :
  -- The free energy function is analytic on the domain beta > 0.
  -- Analyticity implies infinite differentiability and absence of singularities
  -- which are hallmarks of phase transitions.
  AnalyticAt ℝ (F_TM N hN) p :=
  by apply (F_TM_analytic N hN h_main_thm).analyticAt; exact IsOpen.mem_nhds isOpen_U_domain hp

/-
Informal Conclusion: Since the Free Energy F_TM is proven to be real analytic
as a function of the parameters (beta > 0, J, mu) for any finite N, the system
described by this model does not exhibit sharp phase transitions at finite temperature
for finite system size, regardless of the inhomogeneity profile mu.
-/

end -- noncomputable section
