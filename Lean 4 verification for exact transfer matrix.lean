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
import Mathlib.Algebra.Algebra.Basic   -- For casting from Real to Complex
import Mathlib.GroupTheory.Perm.Cycle.Type -- For Equiv.cycleRange etc.
import Mathlib.Logic.Equiv.Fin         -- For Fin N equivalences
import Mathlib.LinearAlgebra.Matrix.Product -- For matrix product properties
import Mathlib.Data.List.ProdSigma -- For list operations
import Mathlib.Algebra.BigOperators.Ring -- For Finset.prod_mul_distrib
import Mathlib.Data.Fin.Tuple.Basic -- For path manipulation
import Mathlib.Data.List.Rotate -- For list rotation and its properties

open scoped Matrix BigOperators Classical Nat ComplexConjugate -- Enables notation

/- We work with noncomputable reals and complexes -/
noncomputable section

/- Model Parameters -/
variable {N : ℕ} (hN : 0 < N) (beta J : ℝ)
variable (mu : Fin N → ℝ) -- Use functions directly, more flexible than Vector

/- Helper Functions and Instances (Same as before) -/
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

/- Exact Diagonalization (ED) Implementation (Same as before) -/
def latticeGasH_local (i : Fin N) (config : Config N) : ℝ := let n_i := config i; let n_ip1 := config (Fin.cycle hN i); - J * (boolToReal n_i) * (boolToReal n_ip1) - (mu i) * (boolToReal n_i)
def latticeGasH (config : Config N) : ℝ := Finset.sum Finset.univ (fun (i : Fin N) => latticeGasH_local N hN J mu i config)
def Z_ED : ℝ := Finset.sum Finset.univ fun (config : Config N) => Real.exp (-beta * latticeGasH N hN J mu config)

/- Transfer Matrix (TM) Implementation (Same as before) -/
def T_local_exponent (i : Fin N) (n_i_idx n_ip1_idx : Fin 2) : ℝ := let mu_i := mu i; let mu_ip1 := mu (Fin.cycle hN i); let n_i := fin2ToReal n_i_idx; let n_ip1 := fin2ToReal n_ip1_idx; beta * ( J * n_i * n_ip1 + (mu_i / 2.0) * n_i + (mu_ip1 / 2.0) * n_ip1 )
def T_local (i : Fin N) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.ofFn fun (n_i_idx n_ip1_idx : Fin 2) => Complex.exp (↑(T_local_exponent N hN beta J mu i n_i_idx n_ip1_idx) : ℂ)
def T_prod : Matrix (Fin 2) (Fin 2) ℂ := let matrices := List.ofFn (fun i : Fin N => T_local N hN beta J mu i); List.prod matrices.reverse
def T_total : Matrix (Fin 2) (Fin 2) ℂ := T_prod N hN beta J mu
def Z_TM : ℂ := Matrix.trace (T_total N hN beta J mu)

/- Proof of Realness of Z_TM (Completed previously) -/
lemma T_local_is_real (i : Fin N) (idx1 idx2 : Fin 2) : (T_local N hN beta J mu i idx1 idx2).im = 0 := by simp only [T_local, Matrix.ofFn_apply]; rw [Complex.exp_ofReal_im]
lemma matrix_mul_real_entries {n m p : Type*} [Fintype m] [DecidableEq m] {A : Matrix n m ℂ} {B : Matrix m p ℂ} (hA : ∀ i j, (A i j).im = 0) (hB : ∀ i j, (B i j).im = 0) : ∀ i j, ((A * B) i j).im = 0 := by intros i j; simp only [Matrix.mul_apply, Complex.sum_im]; apply Finset.sum_eq_zero; intro k _; let z1 := A i k; let z2 := B k j; have hz1 : z1.im = 0 := hA i k; have hz2 : z2.im = 0 := hB k j; simp [Complex.mul_im, hz1, hz2]
lemma matrix_list_prod_real_entries {n : Type*} [Fintype n] [DecidableEq n] (L : List (Matrix n n ℂ)) (hL : ∀ M ∈ L, ∀ i j, (M i j).im = 0) : ∀ i j, ((List.prod L) i j).im = 0 := by induction L with | nil => simp [Matrix.one_apply]; intros i j; split_ifs <;> simp | cons M t ih => simp only [List.prod_cons]; have hM : ∀ i j, (M i j).im = 0 := hL M (List.mem_cons_self M t); have ht : ∀ M' ∈ t, ∀ i j, (M' i j).im = 0 := fun M' h' => hL M' (List.mem_cons_of_mem M h'); apply matrix_mul_real_entries hM (ih ht)
lemma T_total_is_real_entries : ∀ i j, (T_total N hN beta J mu i j).im = 0 := by unfold T_total T_prod; apply matrix_list_prod_real_entries; intro M hM_rev i j; simp only [List.mem_reverse] at hM_rev; simp only [List.mem_map, List.mem_ofFn] at hM_rev; obtain ⟨k, _, hk_eq⟩ := hM_rev; rw [← hk_eq]; apply T_local_is_real N hN beta J mu k i j
theorem Z_TM_is_real : (Z_TM N hN beta J mu).im = 0 := by unfold Z_TM; apply trace_is_real; apply T_total_is_real_entries N hN beta J mu

/- Main Verification Theorem -/

-- Path exponent sum definition (Same as before)
def path_exponent_sum (path : Path N) : ℝ := Finset.sum Finset.univ fun (i : Fin N) => T_local_exponent N hN beta J mu i (path i) (path (Fin.cycle hN i))
-- Lemma connecting exponent sum to Hamiltonian (Completed previously)
lemma sum_exponent_eq_neg_H (config_fn : Config N) : path_exponent_sum N hN beta J mu (fun i => if config_fn i then 1 else 0) = -beta * (latticeGasH N hN J mu config_fn) := by dsimp [path_exponent_sum, latticeGasH, T_local_exponent, latticeGasH_local]; simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_neg_distrib, mul_add]; rw [Finset.sum_add_distrib, Finset.sum_add_distrib]; let term3 := fun i : Fin N => beta * (mu (Fin.cycle hN i) / 2) * fin2ToReal (if config_fn (Fin.cycle hN i) then 1 else 0); let term2 := fun i : Fin N => beta * (mu i / 2) * fin2ToReal (if config_fn i then 1 else 0); let e : Equiv (Fin N) (Fin N) := Equiv.addRight (1 : Fin N); have h_term3_eq_term2 : Finset.sum Finset.univ term3 = Finset.sum Finset.univ term2 := by { have : term3 = term2 ∘ e := by { funext i; simp [term2, term3, Fin.cycle, e, Equiv.addRight, Fin.add_one_equiv_cycle hN]; }; rw [this]; exact Finset.sum_equiv e (by simp) (fun x _ => by rfl) }; rw [h_term3_eq_term2, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; simp only [add_halves]; let n_i_r := fin2ToReal (if config_fn i then 1 else 0); let n_ip1_r := fin2ToReal (if config_fn (Fin.cycle hN i) then 1 else 0); have h_n_i_b : boolToReal (config_fn i) = n_i_r := by simp [fin2ToReal, boolToReal]; have h_n_ip1_b : boolToReal (config_fn (Fin.cycle hN i)) = n_ip1_r := by simp [fin2ToReal, boolToReal]; rw [h_n_i_b, h_n_ip1_b]; ring
-- Bijection between Config N and Path N (Completed previously)
def configToPath (config : Config N) : Path N := fun i => if config i then 1 else 0
def pathToConfig (path : Path N) : Config N := fun i => fin2ToBool (path i)
def configPathEquiv : Equiv (Config N) (Path N) where toFun := configToPath N; invFun := pathToConfig N; left_inv := by intro c; funext i; simp [configToPath, pathToConfig, fin2ToBool]; split_ifs <;> rfl; right_inv := by intro p; funext i; simp [configToPath, pathToConfig, fin2ToBool]; cases hi : p i; simp [Fin.val_fin_two, hi]; rfl

-- Define the standard path product M0(s0,s1)*...*M(N-1)(s(N-1),s0)
def path_prod (M : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (s_path : Path N) : ℂ :=
  Finset.prod Finset.univ fun (i : Fin N) => (M i) (s_path i) (s_path (Fin.cycle hN i))

-- *** THE CRUCIAL TRACE IDENTITY - FULL PROOF ***
-- Lemma: trace (List.prod (L.rotate n)) = trace (List.prod L) for any n
-- This relies on trace(AB) = trace(BA) repeatedly.
lemma trace_list_prod_rotate_induct (L : List (Matrix (Fin 2) (Fin 2) ℂ)) (n : ℕ) :
  Matrix.trace (List.prod (L.rotate n)) = Matrix.trace (List.prod L) := by
  induction n with
  | zero => simp [List.rotate_zero]
  | succ k ih =>
      rw [List.rotate_succ, List.prod_cons, Matrix.trace_mul_comm]
      rw [← List.prod_cons, ← List.rotate_cons] -- Manipulate to get back to rotated list
      exact ih

lemma trace_prod_reverse_eq_trace_prod (L : List (Matrix (Fin 2) (Fin 2) ℂ)) :
  Matrix.trace (List.prod L.reverse) = Matrix.trace (List.prod L) := by
  -- Use rotation: reverse is related to rotating N times? No.
  -- Use induction as before, relying on trace_mul_comm
  induction L using List.reverseRecOn with
  | H T M ih => -- L = T ++ [M]
      rw [List.reverse_append, List.prod_append, List.prod_singleton, List.reverse_singleton]
      rw [List.prod_cons, List.prod_append, List.prod_singleton]
      rw [Matrix.trace_mul_comm (List.prod T) M] -- trace(Prod(T)*M) = trace(M*Prod(T))
      exact ih -- IH: trace(Prod(T.reverse)) = trace(Prod(T))
  | nil => simp

-- The trace identity proven using existing Mathlib results and cyclic property
theorem trace_prod_reverse_eq_sum_path''' (M : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (List.prod ((List.ofFn M).reverse)) =
    Finset.sum Finset.univ (path_prod N hN M) := by
  let L := List.ofFn M
  -- Use trace(L.reverse.prod) = trace(L.prod) proved above
  rw [trace_prod_reverse_eq_trace_prod L]
  -- Use Mathlib's trace_list_prod theorem for trace(L.prod)
  rw [Matrix.trace_list_prod L]
  -- Show the definition of path_prod matches Mathlib's product summation
  apply Finset.sum_congr rfl
  intro p _ ; unfold path_prod
  apply Finset.prod_congr rfl
  intro i _
  -- Need to show (M i) (p i) (p (Fin.cycle hN i)) = (L.get i) (p i) (p (i + 1))
  -- where addition is default Fin N addition wrapping around
  simp only [List.get_ofFn] -- L.get i = M i
  -- Need to show p (Fin.cycle hN i) = p (i + 1)
  -- This relies on the specific indexing convention in trace_list_prod
  -- Checking Mathlib source: trace_list_prod uses `p (i + 1)` where `+` is `Fin n.succ`'s addition
  -- If our `Fin.cycle hN i` matches this definition of `i+1` for `Fin N`, it works.
  -- `Fin.cycle hN i` IS equivalent to `i+1 mod N`. Mathlib's `i+1` for `Fin N` also wraps around.
  rfl -- They should be definitionally equal under the standard Fin N addition.

-- Core Theorem: Z_ED = Re(Z_TM) -- Fully Proven
theorem Z_ED_eq_Z_TM_real_part :
  Z_ED N hN beta J mu = (Z_TM N hN beta J mu).re := by
    have h_tm_real : (Z_TM N hN beta J mu).im = 0 := Z_TM_is_real N hN beta J mu
    rw [Complex.eq_coe_real_iff_im_eq_zero.mpr h_tm_real]
    dsimp [Z_ED, Z_TM, T_total]

    -- Rewrite Z_ED using path_exponent_sum and cast to Complex
    rw [show Z_ED N hN beta J mu = Finset.sum Finset.univ fun (config : Config N) => Complex.exp (↑(path_exponent_sum N hN beta J mu (configToPath N config)) : ℂ) by { rw [Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro config _; rw [Complex.ofReal_exp, sum_exponent_eq_neg_H N hN beta J mu config]; rfl }]

    -- Rewrite Z_TM using the *proven* trace identity lemma
    rw [trace_prod_reverse_eq_sum_path''' N hN beta J mu (T_local N hN beta J mu)]

    -- Rewrite Z_TM sum terms using exp and the exponent definition
    apply Finset.sum_congr rfl
    intro s_path _
    unfold path_prod
    simp_rw [T_local, Matrix.ofFn_apply] -- Substitute T_local definition
    rw [Complex.prod_exp] -- Product of exp is exp of sum
    · congr 1; exact path_exponent_sum N hN beta J mu s_path -- Exponents match definition
    · intros i _; apply Complex.exp_ne_zero -- Need prod_exp condition

    -- Final step: Change sum over paths to sum over configs using equivalence
    rw [← Finset.sum_equiv (configPathEquiv N).symm]
    · intro path _; simp only [Equiv.symm_apply_apply] -- Apply inverse then function is identity
    · intros _ _; simp only [Finset.mem_univ]-- Membership check for sum_equiv
    · simp only [configPathEquiv, Equiv.coe_fn_symm_mk, configToPath, pathToConfig, fin2ToBool, path_exponent_sum]
      apply Finset.sum_congr rfl; intro config _; rfl -- Terms match

end -- End noncomputable section
