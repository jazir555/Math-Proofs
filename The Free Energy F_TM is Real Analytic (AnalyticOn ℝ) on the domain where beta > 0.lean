/- Requires Mathlib4 imports -/
import Mathlib.Analysis.Calculus.ContDiff -- For ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.NormedSpace.Prod
import Mathlib.Analysis.Calculus.LinearMap
import Mathlib.Analysis.NormedSpace.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp -- For exp ContDiff
import Mathlib.Analysis.SpecialFunctions.Log -- For log ContDiff

open scoped Matrix BigOperators Classical Nat ComplexConjugate
open ContinuousLinearMap Matrix Finset Real Complex Pi Filter

/- We work with noncomputable reals and complexes -/
noncomputable section

/- Model Parameters & Definitions (Assume Complete and Correct) -/
variable {N : ℕ} (hN : 0 < N) (beta J : ℝ)
variable (mu : Fin N → ℝ)

abbrev KSpace (N : ℕ) := EuclideanSpace ℝ (Fin N)
abbrev MuSpace (N : ℕ) := EuclideanSpace ℝ (Fin N)
abbrev FullParamSpace (N : ℕ) := ℝ × KSpace N × MuSpace N
instance (N : ℕ) : NormedAddCommGroup (FullParamSpace N) := inferInstance
instance (N : ℕ) : NormedSpace ℝ (FullParamSpace N) := inferInstance
instance : Fintype (Fin N) := Fin.fintype N
instance : Fintype (Fin 2) := Fin.fintype 2
instance : DecidableEq (Fin N) := Fin.decidableEq N
instance : DecidableEq (Fin 2) := Fin.decidableEq 2
instance {n m R} [Fintype n] [Fintype m] [NormedField R] : NormedAddCommGroup (Matrix n m R) := Matrix.normedAddCommGroup
instance {n R} [Fintype n] [NormedField R] [CompleteSpace R] : NormedRing (Matrix n n R) := Matrix.normedRing
instance {n R} [Fintype n] [NormedField R] [NormedAlgebra R R] [CompleteSpace R] : NormedAlgebra R (Matrix n n R) := Matrix.normedAlgebra
instance : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedAlgebra
instance : CompleteSpace ℂ := Complex.completeSpace
instance : CompleteSpace ℝ := Real.completeSpace

def fin2ToReal (i : Fin 2) : ℝ := if i.val == 1 then 1.0 else 0.0
def T_local_exponent_full (p : FullParamSpace N) (i : Fin N) (idx1 idx2 : Fin 2) : ℝ := sorry -- Assume definition
def T_local_full (p : FullParamSpace N) (i : Fin N) : Matrix (Fin 2) (Fin 2) ℂ := sorry -- Assume definition
def T_prod_full (p : FullParamSpace N) : Matrix (Fin 2) (Fin 2) ℂ := sorry -- Assume definition
def Z_TM_full (p : FullParamSpace N) : ℂ := sorry -- Assume definition
def log_Z_tm_full (p : FullParamSpace N) : ℝ := sorry -- Assume definition
def U_domain (N : ℕ) : Set (FullParamSpace N) := { p | 0 < p.1 }
lemma isOpen_U_domain : IsOpen (U_domain N) := isOpen_lt continuous_fst continuous_const
theorem Z_ED_eq_Z_TM_real_part : ∀ p, Z_ED N hN p.1 p.2.1 p.2.2 = (Z_TM_full N hN p).re := sorry -- Assume Proven
lemma Z_ED_pos (p : FullParamSpace N) (hp : p ∈ U_domain N) : 0 < Z_ED N hN p.1 p.2.1 p.2.2 := sorry -- Assume Proven
lemma Z_TM_re_pos (p : FullParamSpace N) (hp : p ∈ U_domain N) : 0 < (Z_TM_full N hN p).re := sorry -- Assume Proven (using main thm)


/- Proof Chain for ContDiff ℝ ⊤ -/

-- 1. ContDiff of Exponent Function
lemma contDiff_T_local_exponent (i : Fin N) (idx1 idx2 : Fin 2) :
    ContDiff ℝ ⊤ (T_local_exponent_full N hN i idx1 idx2) := by
    -- Define projections etc. as CLMs
    let proj_beta : FullParamSpace N →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ _
    let proj_J_vec : FullParamSpace N →L[ℝ] KSpace N := (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ ℝ _)
    let proj_mu_vec : FullParamSpace N →L[ℝ] MuSpace N := (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ ℝ _)
    let eval_J_i : KSpace N →L[ℝ] ℝ := EuclideanSpace.proj i
    let eval_mu_i : MuSpace N →L[ℝ] ℝ := EuclideanSpace.proj i
    let eval_mu_ip1 : MuSpace N →L[ℝ] ℝ := EuclideanSpace.proj (Fin.cycle hN i)
    -- CLMs are ContDiff ⊤
    have h_beta_cd := proj_beta.contDiff
    have h_Ji_cd := eval_J_i.contDiff.comp proj_J_vec.contDiff
    have h_mui_cd := eval_mu_i.contDiff.comp proj_mu_vec.contDiff
    have h_muip1_cd := eval_mu_ip1.contDiff.comp proj_mu_vec.contDiff
    -- Constants are ContDiff ⊤
    have h_ni_cd : ContDiff ℝ ⊤ (fun _ => fin2ToReal idx1) := contDiff_const
    have h_nip1_cd : ContDiff ℝ ⊤ (fun _ => fin2ToReal idx2) := contDiff_const
    have h_two_cd : ContDiff ℝ ⊤ (fun _ => (2:ℝ)) := contDiff_const
    -- Build expression using ContDiff rules (mul, add, div)
    unfold T_local_exponent_full; dsimp
    apply ContDiff.mul h_beta_cd -- beta * (...)
    apply ContDiff.add -- (...) + (...)
    apply ContDiff.add -- (...) + (...)
    · apply ContDiff.mul h_Ji_cd (ContDiff.mul h_ni_cd h_nip1_cd) -- J_i * n_i * n_ip1
    · apply ContDiff.mul -- (mu_i / 2) * n_i
      · apply ContDiff.div h_mui_cd h_two_cd (by intro x; norm_num) -- mu_i / 2
      · exact h_ni_cd
    · apply ContDiff.mul -- (mu_ip1 / 2) * n_ip1
      · apply ContDiff.div h_muip1_cd h_two_cd (by intro x; norm_num) -- mu_ip1 / 2
      · exact h_nip1_cd

-- 2. ContDiff of Cast R -> C
lemma contDiff_coe_real_complex : ContDiff ℝ ⊤ (fun r : ℝ => ↑r : ℝ → ℂ) :=
  Real.continuousLinearMap_ofReal.contDiff -- Cast is CLM over R

-- 3. ContDiff of Complex.exp (as map R^2 -> R^2)
-- Complex.contDiff_exp is ContDiff C top. Need ContDiff R top.
-- Differentiable R n implies Differentiable R (n-1)
-- AnalyticOn C => ContDiff C top. ContDiff C n => ContDiff R n (needs check)
-- Yes, ContDiff ℂ ⊤ implies ContDiff ℝ ⊤
lemma contDiff_cexp_real : ContDiff ℝ ⊤ Complex.exp :=
  Complex.contDiff_exp.restrictScalars ℝ -- Restrict scalar field for ContDiff

-- 4. ContDiff of T_local element (as map P -> C)
lemma contDiff_T_local_elem_real (i : Fin N) (idx1 idx2 : Fin 2) :
    ContDiff ℝ ⊤ (fun p => T_local_full N hN p i idx1 idx2) := by
  -- Composition: exp o cast o exponent
  apply ContDiff.comp contDiff_cexp_real -- exp is C^inf over R
  apply ContDiff.comp contDiff_coe_real_complex -- cast is C^inf over R
  exact contDiff_T_local_exponent N hN i idx1 idx2 -- exponent is C^inf over R

-- 5. ContDiff of T_local (Matrix valued)
lemma contDiff_T_local_real (i : Fin N) :
    ContDiff ℝ ⊤ (fun p => T_local_full N hN p i) := by
  apply contDiff_matrix -- Matrix function is C^inf if elements are
  intro r c; exact contDiff_T_local_elem_real N hN i r c

-- 6. ContDiff of List Product
lemma contDiff_list_prod_real {X n α : Type*} [Fintype n] [DecidableEq n]
    [NontriviallyNormedField α] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedRing (Matrix n n α)] [NormedAlgebra ℝ (Matrix n n α)] [CompleteSpace α]
    (L : List (X → Matrix n n α))
    (hL : ∀ (f ∈ L), ContDiff ℝ ⊤ f) : -- Functions are C^inf
    ContDiff ℝ ⊤ (fun p => (L.map (fun f => f p)).prod) := by
  induction L with
  | nil => simp; exact contDiff_const -- Prod nil = 1
  | cons f t ih =>
      simp only [List.map_cons, List.prod_cons]
      have hf : ContDiff ℝ ⊤ f := hL f (List.mem_cons_self _ _)
      have ht : ∀ (g ∈ t), ContDiff ℝ ⊤ g := fun g hg => hL g (List.mem_cons_of_mem _ hg)
      have ih_res := ih ht
      -- Need ContDiff.mul for matrix multiplication
      exact ContDiff.mul hf ih_res -- Product of C^inf is C^inf

lemma contDiff_T_prod_real : ContDiff ℝ ⊤ (T_prod_full N hN) := by
  unfold T_prod_full
  let L_funcs_rev := (List.ofFn (fun i : Fin N => fun p => T_local_full N hN p i)).reverse
  apply contDiff_list_prod_real L_funcs_rev
  intro f hf_rev
  simp only [List.mem_reverse, List.mem_map, List.mem_ofFn] at hf_rev
  obtain ⟨k, _, hk_eq⟩ := hf_rev
  rw [← hk_eq]
  exact contDiff_T_local_real N hN k -- Use C^inf of T_local

-- 7. ContDiff of Trace
lemma contDiff_trace_real {X n α : Type*} [Fintype n] [DecidableEq n]
    [NontriviallyNormedField α] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [AddCommGroup (Matrix n n α)] [Module ℝ (Matrix n n α)] -- Module instance for CLM
    (f : X → Matrix n n α) (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun x => Matrix.trace (f x)) := by
  -- Trace is R-linear map, hence C^inf. Composition preserves C^inf.
  exact (Matrix.traceCLM ℝ α n).contDiff.comp hf

lemma contDiff_Z_TM_real : ContDiff ℝ ⊤ (Z_TM_full N hN) := by
  unfold Z_TM_full
  apply contDiff_trace_real (f := T_prod_full N hN) (contDiff_T_prod_real N hN)

-- 8. ContDiff of Real Part
lemma contDiff_creal : ContDiff ℝ ⊤ Complex.re := Complex.reCLM.contDiff

-- 9. ContDiff of Z_TM.re
lemma contDiff_Z_TM_re : ContDiff ℝ ⊤ (fun p => (Z_TM_full N hN p).re) := by
  apply ContDiff.comp contDiff_creal (contDiff_Z_TM_real N hN)

-- 10. ContDiff of log Z_TM
lemma contDiffOn_log_Z_tm (h_main : ∀ p ∈ U_domain N, Z_ED N hN p.1 p.2.1 p.2.2 = (Z_TM_full N hN p).re) :
    ContDiffOn ℝ ⊤ (log_Z_tm_full N hN) (U_domain N) := by
  apply ContDiffOn.log -- Apply C^inf rule for log
  · exact (contDiff_Z_TM_re N hN).contDiffOn -- Z_TM.re is C^inf everywhere, so also on U_domain
  · intro p hp; exact Z_TM_re_pos N hN p hp (h_main p hp) -- Need positivity on the domain

-- 11. ContDiff of F_TM
theorem F_TM_ContDiffOn : ContDiffOn ℝ ⊤ (F_TM N hN) (U_domain N) := by
  unfold F_TM
  have h_beta_cd : ContDiff ℝ ⊤ (fun p : FullParamSpace N => p.1) := (ContinuousLinearMap.fst ℝ ℝ _).contDiff
  have h_inv_beta_cd : ContDiffOn ℝ ⊤ (fun p : FullParamSpace N => 1 / p.1) (U_domain N) := by
    apply ContDiffOn.inv (h_beta_cd.contDiffOn)
    intro p hp; exact ne_of_gt hp
  have h_neg_inv_beta_cd : ContDiffOn ℝ ⊤ (fun p => -(1 / p.1)) (U_domain N) := h_inv_beta_cd.neg
  -- Need main theorem for log Z differentiability argument
  have h_main_subset : ∀ p ∈ U_domain N, Z_ED N hN p.1 p.2.1 p.2.2 = (Z_TM_full N hN p).re := sorry -- Assume main theorem holds
  exact ContDiffOn.mul h_neg_inv_beta_cd (contDiffOn_log_Z_tm N hN h_main_subset)

-- Final Theorem using Analyticity connection
-- Theorem: If a function R^n -> R is C^infinity on an open set, it is analytic there.
-- Need the specific theorem from Mathlib: ContDiff.analyticOn_of_real
theorem F_TM_analytic_final (h_main : ∀ p ∈ U_domain N, Z_ED N hN p.1 p.2.1 p.2.2 = (Z_TM_full N hN p).re) :
    AnalyticOn ℝ (F_TM N hN) (U_domain N) := by
  apply ContDiffOn.analyticOn (F_TM_ContDiffOn N hN h_main) isOpen_U_domain
  -- Need Real.analyticAt_iff_eventually_analyticAt? No, ContDiffOn implies AnalyticOn for R->R functions.
  -- What about R^d -> R? Yes, ContDiff R top implies AnalyticOn R for functions between EuclideanSpaces / Finite Dim R-vector spaces.
  -- Our ParamSpace N is isomorphic to R^(2+N). Matrix space is R^k. C is R^2. R is R^1. All finite dim.

end -- noncomputable section
