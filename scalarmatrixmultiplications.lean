-- mathlib4_global_instances: off

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Trace -- For Matrix.trace
import Mathlib.Algebra.BigOperators.Basic -- For Finset.sum
import Mathlib.Tactic.Linarith -- For solving inequalities
import Mathlib.Tactic.Ring -- For simplifying ring expressions
import Mathlib.Algebra.Module.Basic -- For smul properties
import Mathlib.LinearAlgebra.Pi -- For col definition as a linear map

/-!
# Iterative Lean Formalization for Matrix Multiplication Algorithm Reduction

This file contains the accumulated Lean code from multiple iterations, aiming to
formalize the concepts needed to represent a matrix multiplication tensor decomposition
and to verify rank-reduction transformations.

The ultimate goal (highly ambitious for this format) is to lay groundwork that
could, in principle, support verifying a reduction of a 4x4 matrix multiplication
algorithm from 48 to 47 scalar multiplications.

Current state:
- Basic types for dimensions, matrices, and complex numbers.
- Flattening functions for matrix indices with proofs.
- A structure for `TensorDecomposition` (U, V, W factors).
- A proposition `computes_mat_mul_4x4` to assert a decomposition is correct.
- Structures for rank-reduction patterns (`MergeableColumnsEW`, `BrentPattern1EW`, etc.) defined element-wise.
- Functions to apply these reductions (`remove_matrix_col`, `modify_W_...`, `apply_..._reduction`).
- Stated correctness theorems for these reductions (proofs are `sorry` or in progress).
- Significant progress on `theorem_merged_decomposition_correct`, including key algebraic lemmas
  and the crucial sum re-indexing lemma `sum_bij_remove_k_modify_j`.
-/

open Matrix BigOperators Fin Classical
set_option linter.unusedVariables false -- Allow unused variables for structure fields

-- ## 1. Basic Types and Dimensions

def K : Type := Complex ℝ

def n_dim : ℕ := 4
def m_dim : ℕ := 4
def p_dim : ℕ := 4

lemma n_dim_pos : 0 < n_dim := by decide
lemma m_dim_pos : 0 < m_dim := by decide
lemma p_dim_pos : 0 < p_dim := by decide

def nm_flat_dim : ℕ := n_dim * m_dim
abbrev IdxNMFlat := Fin nm_flat_dim
lemma nm_flat_dim_pos : 0 < nm_flat_dim := Nat.mul_pos n_dim_pos m_dim_pos

def mp_flat_dim : ℕ := m_dim * p_dim
abbrev IdxMPFlat := Fin mp_flat_dim
lemma mp_flat_dim_pos : 0 < mp_flat_dim := Nat.mul_pos m_dim_pos p_dim_pos

def np_flat_dim : ℕ := n_dim * p_dim
abbrev IdxNPFlat := Fin np_flat_dim
lemma np_flat_dim_pos : 0 < np_flat_dim := Nat.mul_pos n_dim_pos p_dim_pos

abbrev MatIdxN := Fin n_dim
abbrev MatIdxM := Fin m_dim
abbrev MatIdxP := Fin p_dim

abbrev Matrix4x4 := Matrix MatIdxN MatIdxM K -- A, B (assuming square for now for simplicity in A,B types)

abbrev FactorMatU (R : ℕ) := Matrix IdxNMFlat (Fin R) K
abbrev FactorMatV (R : ℕ) := Matrix IdxMPFlat (Fin R) K
abbrev FactorMatW (R : ℕ) := Matrix IdxNPFlat (Fin R) K

structure TensorDecomposition (R : ℕ) where
  U : FactorMatU R
  V : FactorMatV R
  W : FactorMatW R
  rank_val : ℕ := R
  rank_pos : R > 0

-- ## 2. Flattening Functions

def flatten_idx (row_dim col_dim : ℕ) (h_col_dim_pos : 0 < col_dim)
    (i : Fin row_dim) (j : Fin col_dim) : Fin (row_dim * col_dim) :=
  ⟨i.val * col_dim + j.val,
   calc
     i.val * col_dim + j.val < i.val * col_dim + col_dim   := Nat.add_lt_add_left j.isLt _
     _ = (i.val + 1) * col_dim                           := by rw [Nat.succ_mul]
     _ ≤ row_dim * col_dim                               := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt i.isLt)
  ⟩

def flatten_A_idx (i : MatIdxN) (j : MatIdxM) : IdxNMFlat :=
  flatten_idx n_dim m_dim m_dim_pos i j

def flatten_B_idx (i : MatIdxM) (j : MatIdxP) : IdxMPFlat :=
  flatten_idx m_dim p_dim p_dim_pos i j

-- Flatten C[i_row_C, k_col_C] for accessing W, using the Python scheme:
-- W_row_idx = k_col_C * n_dim + i_row_C
def flatten_W_idx_for_C (i_row_C : MatIdxN) (k_col_C : MatIdxP) : IdxNPFlat :=
  let val := k_col_C.val * n_dim + i_row_C.val
  ⟨val,
   calc
     k_col_C.val * n_dim + i_row_C.val < k_col_C.val * n_dim + n_dim     := Nat.add_lt_add_left i_row_C.isLt _
     _ = (k_col_C.val + 1) * n_dim                                     := by rw [Nat.succ_mul]
     _ ≤ p_dim * n_dim                                                 := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt k_col_C.isLt)
     _ = n_dim * p_dim                                                 := Nat.mul_comm _ _
  ⟩

-- ## 3. Proposition for Correct Matrix Multiplication
variable {R_rank : ℕ} -- Make R_rank a variable for computes_mat_mul_4x4

def computes_mat_mul_4x4 (decomp : TensorDecomposition R_rank) : Prop :=
  ∀ (A_mat : Matrix MatIdxN MatIdxM K) (B_mat : Matrix MatIdxM MatIdxP K),
    let C_expected := A_mat * B_mat
    let C_computed : Matrix MatIdxN MatIdxP K := fun (i_row_C : MatIdxN) (k_col_C : MatIdxP) =>
      Finset.sum (Finset.univ : Finset (Fin decomp.rank_val)) fun (r : Fin decomp.rank_val) =>
        let W_row_idx := flatten_W_idx_for_C i_row_C k_col_C
        let term_W := decomp.W W_row_idx r
        let term_A_sum : K := Finset.sum Finset.univ fun (a_row_A : MatIdxN) =>
                               Finset.sum Finset.univ fun (b_col_A : MatIdxM) =>
                                 let U_row_idx := flatten_A_idx a_row_A b_col_A
                                 (decomp.U U_row_idx r) * (A_mat a_row_A b_col_A)
        let term_B_sum : K := Finset.sum Finset.univ fun (c_row_B : MatIdxM) =>
                               Finset.sum Finset.univ fun (d_col_B : MatIdxP) =>
                                 let V_row_idx := flatten_B_idx c_row_B d_col_B
                                 (decomp.V V_row_idx r) * (B_mat c_row_B d_col_B)
        term_W * term_A_sum * term_B_sum
    C_expected = C_computed

-- ## 4. Rank Reduction Identity Structures (Element-wise definitions)

structure MergeableColumnsEW (R : ℕ)
    (U : FactorMatU R) (V : FactorMatV R)
    (j k : Fin R) (hj_ne_hk : j ≠ k)
    (d e : K) : Prop where
  U_proportional : ∀ (row_idx : IdxNMFlat), U row_idx k = d * U row_idx j
  V_proportional : ∀ (row_idx : IdxMPFlat), V row_idx k = e * V row_idx j

lemma mergeableColumnsEW_iff_mergeableColumns (R : ℕ) (U : FactorMatU R) (V : FactorMatV R)
    (j k : Fin R) (hj_ne_hk : j ≠ k) (d e : K) :
    MergeableColumnsEW R U V j k hj_ne_hk d e ↔
    (col U k = d • col U j ∧ col V k = e • col V j) := by
  constructor
  · intro hEW
    constructor
    · ext row_idx; rw [col_apply, Pi.smul_apply, col_apply]; exact hEW.U_proportional row_idx
    · ext row_idx; rw [col_apply, Pi.smul_apply, col_apply]; exact hEW.V_proportional row_idx
  · intro hOld
    constructor
    · intro row_idx; rw [← col_apply U k row_idx, hOld.1, Pi.smul_apply, col_apply]
    · intro row_idx; rw [← col_apply V k row_idx, hOld.2, Pi.smul_apply, col_apply]

structure BrentPattern1EW (R : ℕ) -- U_k = U_j + U_l; V's equal
    (U : FactorMatU R) (V : FactorMatV R)
    (k j l : Fin R) (h_distinct : k ≠ j ∧ k ≠ l ∧ j ≠ l) : Prop where
  U_sum_cond : ∀ (idx : IdxNMFlat), U idx k = U idx j + U idx l
  V_eq_cond1 : ∀ (idx : IdxMPFlat), V idx k = V idx j
  V_eq_cond2 : ∀ (idx : IdxMPFlat), V idx k = V idx l

structure BrentPattern2EW (R : ℕ) -- U_k = U_j - U_l; V's equal
    (U : FactorMatU R) (V : FactorMatV R)
    (k j l : Fin R) (h_distinct : k ≠ j ∧ k ≠ l ∧ j ≠ l) : Prop where
  U_diff_cond : ∀ (idx : IdxNMFlat), U idx k = U idx j - U idx l
  V_eq_cond1 : ∀ (idx : IdxMPFlat), V idx k = V idx j
  V_eq_cond2 : ∀ (idx : IdxMPFlat), V idx k = V idx l

structure BrentPatternV_sumEW (R : ℕ) -- V_k = V_j + V_l; U's equal
    (U : FactorMatU R) (V : FactorMatV R)
    (k j l : Fin R) (h_distinct : k ≠ j ∧ k ≠ l ∧ j ≠ l) : Prop where
  V_sum_cond : ∀ (idx : IdxMPFlat), V idx k = V idx j + V idx l
  U_eq_cond1 : ∀ (idx : IdxNMFlat), U idx k = U idx j
  U_eq_cond2 : ∀ (idx : IdxNMFlat), U idx k = U idx l

structure BrentPatternV_diffEW (R : ℕ) -- V_k = V_j - V_l; U's equal
    (U : FactorMatU R) (V : FactorMatV R)
    (k j l : Fin R) (h_distinct : k ≠ j ∧ k ≠ l ∧ j ≠ l) : Prop where
  V_diff_cond : ∀ (idx : IdxMPFlat), V idx k = V idx j - V idx l
  U_eq_cond1 : ∀ (idx : IdxNMFlat), U idx k = U idx j
  U_eq_cond2 : ∀ (idx : IdxNMFlat), U idx k = U idx l


-- ## 5. Matrix Column Operations and Decomposition Transformation Functions

def remove_matrix_col {D R : ℕ} (hR_ge_1 : R ≥ 1)
    (M : Matrix (Fin D) (Fin R) K) (k_rem : Fin R) :
    Matrix (Fin D) (Fin (R - 1)) K :=
  fun (d_idx : Fin D) (j_new : Fin (R - 1)) =>
    let old_idx_val := if j_new.val < k_rem.val then j_new.val else j_new.val + 1
    have h_old_idx_bound : old_idx_val < R := by
      simp only
      split_ifs with h_cond_lt
      · exact Nat.lt_of_lt_of_le h_cond_lt k_rem.isLt.le
      · exact Nat.succ_lt_succ_iff.mpr j_new.isLt
    M d_idx ⟨old_idx_val, h_old_idx_bound⟩

def modify_W_col_for_merge {nrows R : ℕ} (hR_pos : R > 0)
    (W_orig : Matrix (Fin nrows) (Fin R) K)
    (j_mod k_merged : Fin R) (_hj_ne_hk : j_mod ≠ k_merged)
    (merge_coeff : K) :
    Matrix (Fin nrows) (Fin R) K :=
  fun r c => if c = j_mod then
               W_orig r j_mod + merge_coeff * W_orig r k_merged
             else
               W_orig r c

noncomputable def apply_merge_reduction {R_orig : ℕ} (hR_orig_gt_1 : R_orig > 1)
    (orig_decomp : TensorDecomposition R_orig)
    (j k : Fin R_orig) (hj_ne_hk : j ≠ k) (d e : K)
    (h_mergeable : MergeableColumnsEW R_orig orig_decomp.U orig_decomp.V j k hj_ne_hk d e) :
    TensorDecomposition (R_orig - 1) :=
  let R_new := R_orig - 1
  have hR_new_pos : R_new > 0 := Nat.sub_pos_of_lt hR_orig_gt_1
  have hR_orig_ge_1 : R_orig ≥ 1 := Nat.le_of_lt hR_orig_gt_1
  let U_new := remove_matrix_col hR_orig_ge_1 orig_decomp.U k
  let V_new := remove_matrix_col hR_orig_ge_1 orig_decomp.V k
  let W_modified_for_j := modify_W_col_for_merge orig_decomp.rank_pos orig_decomp.W j k hj_ne_hk (d * e)
  let W_new := remove_matrix_col hR_orig_ge_1 W_modified_for_j k
  { U := U_new, V := V_new, W := W_new, rank_val := R_new, rank_pos := hR_new_pos }

def modify_W_for_brent1EW {nrows R : ℕ} (hR_pos : R > 0)
    (W_orig : Matrix (Fin nrows) (Fin R) K) (k j l : Fin R) (_h_distinct) :
    Matrix (Fin nrows) (Fin R) K :=
  fun r c => if c = j then W_orig r j + W_orig r k else if c = l then W_orig r l + W_orig r k else W_orig r c

noncomputable def apply_brent1EW_reduction {R_orig : ℕ} (hR_orig_gt_1 : R_orig > 1)
    (orig_decomp : TensorDecomposition R_orig) (k j l : Fin R_orig) (h_distinct)
    (h_brent : BrentPattern1EW R_orig orig_decomp.U orig_decomp.V k j l h_distinct) : TensorDecomposition (R_orig - 1) :=
  let U_new := remove_matrix_col (Nat.le_of_lt hR_orig_gt_1) orig_decomp.U k
  let V_new := remove_matrix_col (Nat.le_of_lt hR_orig_gt_1) orig_decomp.V k
  let W_mod := modify_W_for_brent1EW orig_decomp.rank_pos orig_decomp.W k j l h_distinct
  let W_new := remove_matrix_col (Nat.le_of_lt hR_orig_gt_1) W_mod k
  { U := U_new, V := V_new, W := W_new, rank_val := R_orig - 1, rank_pos := Nat.sub_pos_of_lt hR_orig_gt_1 }

def modify_W_for_brent2EW {nrows R : ℕ} (hR_pos : R > 0)
    (W_orig : Matrix (Fin nrows) (Fin R) K) (k j l : Fin R) (_h_distinct) :
    Matrix (Fin nrows) (Fin R) K :=
  fun r c => if c = j then W_orig r j + W_orig r k else if c = l then W_orig r l - W_orig r k else W_orig r c

noncomputable def apply_brent2EW_reduction {R_orig : ℕ} (hR_orig_gt_1 : R_orig > 1)
    (orig_decomp : TensorDecomposition R_orig) (k j l : Fin R_orig) (h_distinct)
    (h_brent : BrentPattern2EW R_orig orig_decomp.U orig_decomp.V k j l h_distinct) : TensorDecomposition (R_orig - 1) :=
  let U_new := remove_matrix_col (Nat.le_of_lt hR_orig_gt_1) orig_decomp.U k
  let V_new := remove_matrix_col (Nat.le_of_lt hR_orig_gt_1) orig_decomp.V k
  let W_mod := modify_W_for_brent2EW orig_decomp.rank_pos orig_decomp.W k j l h_distinct
  let W_new := remove_matrix_col (Nat.le_of_lt hR_orig_gt_1) W_mod k
  { U := U_new, V := V_new, W := W_new, rank_val := R_orig - 1, rank_pos := Nat.sub_pos_of_lt hR_orig_gt_1 }

def modify_W_for_brentV_sumEW {nrows R : ℕ} (hR_pos : R > 0)
    (W_orig : Matrix (Fin nrows) (Fin R) K) (k j l : Fin R) (h_distinct) :
    Matrix (Fin nrows) (Fin R) K :=
  modify_W_for_brent1EW hR_pos W_orig k j l h_distinct

noncomputable def apply_brentV_sumEW_reduction {R_orig : ℕ} (hR_orig_gt_1 : R_orig > 1)
    (orig_decomp : TensorDecomposition R_orig) (k j l : Fin R_orig) (h_distinct)
    (h_brent : BrentPatternV_sumEW R_orig orig_decomp.U orig_decomp.V k j l h_distinct) : TensorDecomposition (R_orig - 1) :=
  let U_new := remove_matrix_col (Nat.le_of_lt hR_orig_gt_1) orig_decomp.U k
  let V_new := remove_matrix_col (Nat.le_of_lt hR_orig_gt_1) orig_decomp.V k
  let W_mod := modify_W_for_brentV_sumEW orig_decomp.rank_pos orig_decomp.W k j l h_distinct
  let W_new := remove_matrix_col (Nat.le_of_lt hR_orig_gt_1) W_mod k
  { U := U_new, V := V_new, W := W_new, rank_val := R_orig - 1, rank_pos := Nat.sub_pos_of_lt hR_orig_gt_1 }

def modify_W_for_brentV_diffEW {nrows R : ℕ} (hR_pos : R > 0)
    (W_orig : Matrix (Fin nrows) (Fin R) K) (k j l : Fin R) (h_distinct) :
    Matrix (Fin nrows) (Fin R) K :=
  modify_W_for_brent2EW hR_pos W_orig k j l h_distinct

noncomputable def apply_brentV_diffEW_reduction {R_orig : ℕ} (hR_orig_gt_1 : R_orig > 1)
    (orig_decomp : TensorDecomposition R_orig) (k j l : Fin R_orig) (h_distinct)
    (h_brent : BrentPatternV_diffEW R_orig orig_decomp.U orig_decomp.V k j l h_distinct) : TensorDecomposition (R_orig - 1) :=
  let U_new := remove_matrix_col (Nat.le_of_lt hR_orig_gt_1) orig_decomp.U k
  let V_new := remove_matrix_col (Nat.le_of_lt hR_orig_gt_1) orig_decomp.V k
  let W_mod := modify_W_for_brentV_diffEW orig_decomp.rank_pos orig_decomp.W k j l h_distinct
  let W_new := remove_matrix_col (Nat.le_of_lt hR_orig_gt_1) W_mod k
  { U := U_new, V := V_new, W := W_new, rank_val := R_orig - 1, rank_pos := Nat.sub_pos_of_lt hR_orig_gt_1 }

-- ## 6. Correctness Theorems (Stated)

theorem theorem_merged_decomposition_correct {R_orig : ℕ} (hR_orig_gt_1 : R_orig > 1)
    (orig_decomp : TensorDecomposition R_orig)
    (h_orig_correct : computes_mat_mul_4x4 orig_decomp)
    (j k : Fin R_orig) (hj_ne_hk : j ≠ k) (d e : K)
    (h_mergeable : MergeableColumnsEW R_orig orig_decomp.U orig_decomp.V j k hj_ne_hk d e) :
    let new_decomp := apply_merge_reduction hR_orig_gt_1 orig_decomp j k hj_ne_hk d e h_mergeable
    computes_mat_mul_4x4 new_decomp :=
  sorry

theorem theorem_brent1EW_reduction_correct {R_orig : ℕ} (hR_orig_gt_1 : R_orig > 1)
    (orig_decomp : TensorDecomposition R_orig)
    (h_orig_correct : computes_mat_mul_4x4 orig_decomp)
    (k j l : Fin R_orig) (h_distinct : k ≠ j ∧ k ≠ l ∧ j ≠ l)
    (h_brent : BrentPattern1EW R_orig orig_decomp.U orig_decomp.V k j l h_distinct) :
    let new_decomp := apply_brent1EW_reduction hR_orig_gt_1 orig_decomp k j l h_distinct h_brent
    computes_mat_mul_4x4 new_decomp :=
  sorry

theorem theorem_brent2EW_reduction_correct {R_orig : ℕ} (hR_orig_gt_1 : R_orig > 1)
    (orig_decomp : TensorDecomposition R_orig)
    (h_orig_correct : computes_mat_mul_4x4 orig_decomp)
    (k j l : Fin R_orig) (h_distinct : k ≠ j ∧ k ≠ l ∧ j ≠ l)
    (h_brent : BrentPattern2EW R_orig orig_decomp.U orig_decomp.V k j l h_distinct) :
    let new_decomp := apply_brent2EW_reduction hR_orig_gt_1 orig_decomp k j l h_distinct h_brent
    computes_mat_mul_4x4 new_decomp :=
  sorry

theorem theorem_brentV_sumEW_reduction_correct {R_orig : ℕ} (hR_orig_gt_1 : R_orig > 1)
    (orig_decomp : TensorDecomposition R_orig)
    (h_orig_correct : computes_mat_mul_4x4 orig_decomp)
    (k j l : Fin R_orig) (h_distinct : k ≠ j ∧ k ≠ l ∧ j ≠ l)
    (h_brent : BrentPatternV_sumEW R_orig orig_decomp.U orig_decomp.V k j l h_distinct) :
    let new_decomp := apply_brentV_sumEW_reduction hR_orig_gt_1 orig_decomp k j l h_distinct h_brent
    computes_mat_mul_4x4 new_decomp :=
  sorry

theorem theorem_brentV_diffEW_reduction_correct {R_orig : ℕ} (hR_orig_gt_1 : R_orig > 1)
    (orig_decomp : TensorDecomposition R_orig)
    (h_orig_correct : computes_mat_mul_4x4 orig_decomp)
    (k j l : Fin R_orig) (h_distinct : k ≠ j ∧ k ≠ l ∧ j ≠ l)
    (h_brent : BrentPatternV_diffEW R_orig orig_decomp.U orig_decomp.V k j l h_distinct) :
    let new_decomp := apply_brentV_diffEW_reduction hR_orig_gt_1 orig_decomp k j l h_distinct h_brent
    computes_mat_mul_4x4 new_decomp :=
  sorry

-- ## 7. Proof of `theorem_merged_decomposition_correct` (Continued)

lemma term_A_sum_proportional {R : ℕ} (U_mat : FactorMatU R)
    (A_mat : Matrix MatIdxN MatIdxM K) (j k_col : Fin R) (d : K)
    (hU_prop : ∀ (ridx : IdxNMFlat), U_mat ridx k_col = d * U_mat ridx j) :
    (Finset.sum Finset.univ fun (ar:MatIdxN) => Finset.sum Finset.univ fun (bc:MatIdxM) =>
      (U_mat (flatten_A_idx ar bc) k_col) * (A_mat ar bc)) =
    d * (Finset.sum Finset.univ fun (ar:MatIdxN) => Finset.sum Finset.univ fun (bc:MatIdxM) =>
      (U_mat (flatten_A_idx ar bc) j) * (A_mat ar bc)) := by
  simp_rw [hU_prop]
  conv =>
    lhs
    congr; next α_idx =>
    congr; next β_idx =>
    rw [mul_assoc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _;
  rw [Finset.mul_sum]

lemma term_B_sum_proportional {R : ℕ} (V_mat : FactorMatV R)
    (B_mat : Matrix MatIdxM MatIdxP K) (j k_col : Fin R) (e : K)
    (hV_prop : ∀ (ridx : IdxMPFlat), V_mat ridx k_col = e * V_mat ridx j) :
    (Finset.sum Finset.univ fun (cr:MatIdxM) => Finset.sum Finset.univ fun (dc:MatIdxP) =>
      (V_mat (flatten_B_idx cr dc) k_col) * (B_mat cr dc)) =
    e * (Finset.sum Finset.univ fun (cr:MatIdxM) => Finset.sum Finset.univ fun (dc:MatIdxP) =>
      (V_mat (flatten_B_idx cr dc) j) * (B_mat cr dc)) := by
  simp_rw [hV_prop]
  conv =>
    lhs
    congr; next α_idx =>
    congr; next β_idx =>
    rw [mul_assoc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _;
  rw [Finset.mul_sum]

lemma sum_bij_remove_k_modify_j
    {R : ℕ} (hR_ge_1 : R ≥ 1)
    (terms_orig_val : Fin R → K)                             -- Original values for terms
    (W_orig_row : Fin R → K)                                -- W coefficients for the specific C[i,k]
    (k_rem j_mod_orig_idx : Fin R)
    (hj_ne_hk : j_mod_orig_idx ≠ k_rem)
    (merge_val_for_j_mod : K)                               -- This is W_orig(k_rem) * (d*e)
    (terms_new_val : Fin (R-1) → K)                         -- New values for terms in reduced sum
    (W_new_row : Fin (R-1) → K)                             -- New W coefficients
    (h_terms_new_relation : ∀ (j_new : Fin (R-1)),
        terms_new_val j_new = terms_orig_val (Fin.succAbove k_rem j_new))
    (h_W_new_relation : ∀ (j_new : Fin (R-1)),
        let old_idx_mapped := Fin.succAbove k_rem j_new
        W_new_row j_new = if old_idx_mapped = j_mod_orig_idx then
                              W_orig_row j_mod_orig_idx + merge_val_for_j_mod -- Modified W term for j_mod
                          else
                              W_orig_row old_idx_mapped) :
    -- Original sum: ∑_{r≠k} W(r)m(r) + (W(j) + merge_val_for_j_mod)m(j)
    -- This is sum over r≠k, where if r=j, W(r) is replaced by W(j)+merge_val_for_j_mod
    (Finset.sum (Finset.univ.filter (fun r => r ≠ k_rem))
      (fun r_orig => (if r_orig = j_mod_orig_idx then W_orig_row j_mod_orig_idx + merge_val_for_j_mod
                     else W_orig_row r_orig) * terms_orig_val r_orig) )
    =
    ∑ r_new : Fin (R-1), W_new_row r_new * terms_new_val r_new := by
  apply Finset.sum_bij (fun (r_new : Fin (R-1)) _ => Fin.succAbove k_rem r_new)
  · -- Membership: For r_new in univ, finSuccAbove k_rem r_new is in univ.filter (≠ k_rem)
    intro r_new _; simp
    exact Fin.succAbove_ne k_rem r_new
  · -- Goal: (W_new_row r_new * terms_new_val r_new) = RHS integrand at (finSuccAbove k_rem r_new)
    intro r_new _
    simp_rw [h_terms_new_relation, h_W_new_relation]
    rfl -- This holds by definition as terms match up
  · -- Injection: If Fin.succAbove k_rem r1 = Fin.succAbove k_rem r2, then r1 = r2
    intro r1 r2 _ _ h_eq
    exact Fin.succAbove_right_inj k_rem h_eq
  · -- Surjection: For every r_orig in univ.filter (≠ k_rem), there exists r_new s.t. finSuccAbove k_rem r_new = r_orig
    intro r_orig hr_orig_mem
    simp at hr_orig_mem
    use Fin.predAbove k_rem ⟨r_orig, Fin.isLt r_orig⟩
    simp
    exact Fin.succAbove_predAbove_of_ne_cast hr_orig_mem

-- Main theorem proof attempt (continued)
theorem theorem_merged_decomposition_correct_proof_attempt {R_orig : ℕ} (hR_orig_gt_1 : R_orig > 1)
    (orig_decomp : TensorDecomposition R_orig)
    (h_orig_correct : computes_mat_mul_4x4 orig_decomp)
    (j k : Fin R_orig) (hj_ne_hk : j ≠ k) (d e : K)
    (h_mergeable : MergeableColumnsEW R_orig orig_decomp.U orig_decomp.V j k hj_ne_hk d e) :
    let new_decomp := apply_merge_reduction hR_orig_gt_1 orig_decomp j k hj_ne_hk d e h_mergeable
    computes_mat_mul_4x4 new_decomp := by
  dsimp [computes_mat_mul_4x4, apply_merge_reduction]
  intro A_mat B_mat
  let C_expected := A_mat * B_mat

  let term_A_sum_orig (r_idx : Fin orig_decomp.rank_val) : K :=
    ∑ ar, ∑ bc, (orig_decomp.U (flatten_A_idx ar bc) r_idx) * (A_mat ar bc)
  let term_B_sum_orig (r_idx : Fin orig_decomp.rank_val) : K :=
    ∑ cr, ∑ dc, (orig_decomp.V (flatten_B_idx cr dc) r_idx) * (B_mat cr dc)
  let m_orig (r_idx : Fin orig_decomp.rank_val) : K := term_A_sum_orig r_idx * term_B_sum_orig r_idx

  have h_m_orig_k_prop : m_orig k = (d * e) * m_orig j := by
    unfold m_orig
    rw [term_A_sum_proportional orig_decomp.U A_mat j k d h_mergeable.U_proportional]
    rw [term_B_sum_proportional orig_decomp.V B_mat j k e h_mergeable.V_proportional]
    ring

  let C_orig_computed_element (i_C : MatIdxN) (k_C : MatIdxP) : K :=
    ∑ r : Fin orig_decomp.rank_val, (orig_decomp.W (flatten_W_idx_for_C i_C k_C) r) * m_orig r

  have h_C_orig_eq_expected : (fun i k_ => C_orig_computed_element i k_) = C_expected :=
    funext fun i => funext fun k_ => h_orig_correct A_mat B_mat ▸ rfl

  let R_new := orig_decomp.rank_val - 1
  have hR_new_pos : R_new > 0 := Nat.sub_pos_of_lt hR_orig_gt_1
  have hR_orig_ge_1 : R_orig ≥ 1 := Nat.le_of_lt hR_orig_gt_1

  let U_new_def := remove_matrix_col hR_orig_ge_1 orig_decomp.U k
  let V_new_def := remove_matrix_col hR_orig_ge_1 orig_decomp.V k
  let W_modified_for_j := modify_W_col_for_merge orig_decomp.rank_pos orig_decomp.W j k hj_ne_hk (d * e)
  let W_new_def := remove_matrix_col hR_orig_ge_1 W_modified_for_j k

  let term_A_sum_new (r_new_idx : Fin R_new) : K :=
    ∑ ar, ∑ bc, (U_new_def (flatten_A_idx ar bc) r_new_idx) * (A_mat ar bc)
  let term_B_sum_new (r_new_idx : Fin R_new) : K :=
    ∑ cr, ∑ dc, (V_new_def (flatten_B_idx cr dc) r_new_idx) * (B_mat cr dc)
  let m_new (r_new_idx : Fin R_new) : K := term_A_sum_new r_new_idx * term_B_sum_new r_new_idx

  let C_new_computed_element (i_C : MatIdxN) (k_C : MatIdxP) : K :=
    ∑ r_new : Fin R_new, (W_new_def (flatten_W_idx_for_C i_C k_C) r_new) * m_new r_new

  apply funext; intro i_C; apply funext; intro k_C
  rw [← h_C_orig_eq_expected]
  dsimp [C_orig_computed_element]

  let W_row_fixed := flatten_W_idx_for_C i_C k_C

  have h_sum_transformed :
    ∑ r_orig : Fin R_orig, (orig_decomp.W W_row_fixed r_orig) * m_orig r_orig =
    ∑ r_orig ∈ Finset.univ.filter (fun r => r ≠ k), -- Sum over r_orig ≠ k
      (if r_orig = j then (orig_decomp.W W_row_fixed j + (d*e) * orig_decomp.W W_row_fixed k)
      else orig_decomp.W W_row_fixed r_orig) * m_orig r_orig := by
    rw [← Finset.sum_filter_add_sum_filter_eq_sum_if_symm Finset.univ (fun r => r=k)]
    -- sum over r≠k + sum over r=k
    simp only [Finset.sum_filter_False, Finset.sum_empty, add_zero, Finset.filter_true_of_mem, Finset.sum_singleton]
    -- sum_{r≠k} (if r=j then (Wj+deWk)m_orig(j) else W(r)m_orig(r))  +  (if k=j then (Wj+deWk)m_orig(j) else W(k)m_orig(k))
    -- If k=j, this is a contradiction with hj_ne_hk. So `if k=j` is false.
    rw [if_neg hj_ne_hk.symm] -- k is not j
    -- sum_{r≠k} (...) + W(k)m_orig(k)
    -- RHS of goal: sum_{r≠k} (...)
    -- We need to show W(k)m_orig(k) is incorporated.
    -- Original sum is sum_{r!=k, r!=j} W(r)m(r) + W(j)m(j) + W(k)m(k)
    -- Transformed sum is sum_{r!=k, r!=j} W(r)m(r) + (W(j)+(d*e)W(k))m(j)
    -- Difference is (W(j)+(d*e)W(k))m(j) - (W(j)m(j) + W(k)m(k)) = d*e*W(k)m(j) - W(k)m(k)
    -- This should be zero if m(k) = d*e*m(j).
    rw [Finset.sum_eq_add_sum_compl ({k} : Finset (Fin R_orig))]
    simp only [Finset.sum_singleton, Finset.filter_ne]
    rw [h_m_orig_k_prop]
    -- sum_{r≠k} W(r)m(r) + W(k)(d*e)m(j)
    -- Target: sum_{r≠k} (if r=j then (W(j)+(d*e)W(k)) else W(r)) * m_orig(r)
    rw [Finset.sum_ite_eq_add_compl_sub_filter Finset.univ ({j} : Finset (Fin R_orig)) (fun r => r ≠ k)]
    simp only [Finset.sum_singleton, Finset.filter_ne]
    -- (if j=j then (Wj+deWk)m(j) else W(j)m(j)) assuming j≠k
    --  + sum_{r≠k, r≠j} (if r=j then ... else W(r)m(r))
    rw [if_pos rfl]
    -- (Wj+deWk)m(j) + sum_{r≠k, r≠j} W(r)m(r)
    -- This matches the form (∑_{r ≠ j, r ≠ k} W(r)m(org(r))) + (W(j) + (d*e)W(k))m(org(j)) seen before.
    ring_nf -- Simplify and rearrange terms
    rw [add_assoc]
    congr 1
    rw [add_comm]


  rw [h_sum_transformed]
  dsimp [C_new_computed_element] -- Unfold the target sum

  -- Apply sum_bij_remove_k_modify_j
  -- terms_orig_val r := m_orig r
  -- W_orig_row r := if r = j then (orig_decomp.W W_row_fixed j + (d*e) * orig_decomp.W W_row_fixed k)
  --                 else orig_decomp.W W_row_fixed r
  -- coeff_for_j_mod is effectively folded into W_orig_row at j.
  -- terms_new_def r_new := m_new r_new
  -- W_new_row r_new := W_new_def W_row_fixed r_new

  apply @sum_bij_remove_k_modify_j R_orig hR_orig_ge_1
    (fun r => m_orig r) -- terms_orig_val
    W_row_fixed -- This is orig_decomp.W W_row_fixed. Not the modified one.
    k j hj_ne_hk
    ((d*e) * orig_decomp.W W_row_fixed k * m_orig j) -- This is the term added to (W(j)m(j))
                                                     -- No, coeff_for_j_mod is added to terms_orig j_mod_orig_idx
                                                     -- Let terms_orig_val be W(r)*m_orig(r)
    -- This requires a slightly different sum_bij lemma or careful application
  sorry -- Proof requires careful alignment with sum_bij_remove_k_modify_j
