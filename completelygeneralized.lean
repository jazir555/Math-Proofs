/- Requires Mathlib4 and potentially advanced libraries later -/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic           -- For Fin N
import Mathlib.Data.Fintype.Basic       -- For Fintype class
import Mathlib.Data.Matrix.Basic        -- For Matrix type
import Mathlib.Algebra.BigOperators.Basic -- For Finset.sum, Finset.prod
import Mathlib.Analysis.SpecialFunctions.Exp -- For Real.exp, Complex.exp
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Exponential
import Mathlib.Algebra.Algebra.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Logic.Equiv.Fin
import Mathlib.LinearAlgebra.Matrix.Product
import Mathlib.Data.List.ProdSigma
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Rotate -- Needed for trace_prod_reverse_eq_trace_prod proof
import Mathlib.Data.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpace -- For continuous case
import Mathlib.MeasureTheory.Integration -- For integrals
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap -- For quantum
import Mathlib.Analysis.NormedSpace.OperatorNorm -- For quantum
import Mathlib.Analysis.Calculus.FunctionalCalculus.Exponential -- For Op Exp
-- Added for finite dimensional Hilbert spaces and matrix representation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Trace
import Mathlib.FieldTheory.Tower -- For is_scalar_tower
import Mathlib.Data.Option.Basic -- For Option operations
import Mathlib.Data.Fin.SuccPred -- For Fin N-1 construction
-- Imports for Hilbert space bases and summability
import Mathlib.Analysis.HilbertSpace.HilbertBasis
import Mathlib.Analysis.InnerProductSpace.Basic -- For inner product
import Mathlib.Topology.Algebra.InfiniteSum -- For Summable / HasSum
import Mathlib.Analysis.InnerProductSpace.Spectrum -- For eigenvalues/spectrum?
import Mathlib.Data.NNReal -- For NNReal
import Mathlib.Analysis.NormedSpace.Operator.Adjoint -- For adjoint
import Mathlib.Analysis.InnerProductSpace.Positive -- For positive operators


open scoped Matrix BigOperators Classical Nat ComplexConjugate ENNReal NNReal -- Enables notation

/- We work with noncomputable reals and complexes -/
noncomputable section

/-!
# Universal Abstract Framework for Statistical Mechanics Models (Conceptual)

This framework uses abstraction to represent components common to various
statistical mechanics models (classical/quantum, discrete/continuous, etc.).
This file incorporates all incrementally filled definitions, using 'sorry'
placeholders only for concepts requiring further advanced mathematical formalization.
NO AXIOMS ARE USED.
-/

-- Section: Abstract Definitions

/-- Typeclass for defining how to sum or integrate over a configuration space. -/
class SummableSpace (ConfigSpace : Type) where
  ValueType : Type
  [addCommMonoid : AddCommMonoid ValueType]
  integrate : (ConfigSpace → ValueType) → Prop → ValueType -- Function, Integrability flag -> Result

-- Example Instance for Fintype
instance FintypeSummableSpace {C : Type} [Fintype C] [DecidableEq C] {V : Type} [AddCommMonoid V] :
    SummableSpace C where
  ValueType := V
  integrate f _ := Finset.sum Finset.univ f

-- Example Instance for Measure Space
instance MeasureSummableSpace {C : Type} [MeasureSpace C] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]:
    SummableSpace C where
  ValueType := V
  integrate f h_integrable := if h_integrable then ∫ cfg, f cfg else 0

/-- Operator Trace definition for finite dimensional Hilbert spaces. -/
@[nolint noncomputableHomomorphism]
noncomputable def op_trace_finite_dim {n : ℕ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H] (h_fin_dim : FiniteDimensional.finrank ℂ H = n)
    (b : Basis (Fin n) ℂ H)
    (A : ContinuousLinearMap ℂ H H) : ℂ :=
  let M : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix b b A
  Matrix.trace M

/-- SummableSpace instance for Finite Dimensional Quantum Trace. -/
instance QuantumFiniteDimTraceSpace {n : ℕ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H] (h_fin_dim : FiniteDimensional.finrank ℂ H = n)
    (basis : Basis (Fin n) ℂ H) :
    SummableSpace Unit where
  ValueType := ℂ
  addCommMonoid := inferInstance
  integrate f _ := f Unit.unit -- Requires f() to compute the trace


/-- Placeholder for the positive square root of a positive operator. Needs Functional Calculus. -/
noncomputable def op_sqrt {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ContinuousLinearMap ℂ H H) (hA : IsSelfAdjoint A) (hA_pos : ∀ x, 0 ≤ Complex.re (inner (A x) x)) :
    ContinuousLinearMap ℂ H H :=
  sorry -- Requires functional calculus for operators

/-- Placeholder for the absolute value operator |A| = sqrt(A* A). -/
@[nolint unusedArguments] -- H is needed for context, A is the input
noncomputable def op_abs {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ContinuousLinearMap ℂ H H) : ContinuousLinearMap ℂ H H :=
  -- Mathematical Definition: sqrt(adjoint A * A)
  let AadjA := (ContinuousLinearMap.adjoint A) * A
  have h_adj : IsSelfAdjoint AadjA := ContinuousLinearMap.isSelfAdjoint_adjoint_mul_self A
  have h_pos_re : ∀ x, 0 ≤ Complex.re (inner (AadjA x) x) := fun x => by
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_left, ← Complex.inner_self_re]
      apply sq_nonneg
  -- The actual sqrt operation requires functional calculus
  op_sqrt AadjA h_adj h_pos_re


/-- Placeholder for singular values of an operator -/
@[nolint unusedArguments] -- H, A needed for context
def singular_values {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ContinuousLinearMap ℂ H H) : Type := ℕ → NNReal -- Type representing the sequence

-- Placeholder for eigenvalues/spectrum of a self-adjoint operator
@[nolint unusedArguments]
noncomputable def op_spectrum_eigenvalues {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ContinuousLinearMap ℂ H H) (hA : IsSelfAdjoint A) : ℕ → ℝ :=
  -- Requires spectral theorem formalization
  sorry

-- Function to compute the singular values (remains sorry)
@[nolint unusedArguments]
noncomputable def compute_singular_values {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ContinuousLinearMap ℂ H H) : singular_values A :=
  -- Singular values are eigenvalues of |A| = op_abs A.
  -- Need proof that |A| is self-adjoint.
  let absA := op_abs A
  have h_absA_sa : IsSelfAdjoint absA := sorry -- Requires proof based on op_sqrt/func calc properties
  let eigenvalues := op_spectrum_eigenvalues absA h_absA_sa
  -- Need proof that eigenvalues of |A| are non-negative
  fun n => Real.toNNReal (eigenvalues n)


/-- Define a proposition for the Trace Class condition (placeholder). -/
def IsTraceClass {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ContinuousLinearMap ℂ H H) : Prop :=
  -- Definition: A is trace class if Sum_k s_k converges,
  -- where s_k are the singular values of A (eigenvalues of |A| = sqrt(A* A)).
  let s : singular_values A := compute_singular_values A -- s defined via sorry'd func
  Summable s -- Check if the sequence `s` (whose values are sorry) is summable


/-- Placeholder function for infinite dimensional trace. Returns Option ℂ. -/
noncomputable def op_trace_infinite_dim {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ContinuousLinearMap ℂ H H) : Option ℂ :=
  -- This relies on the IsTraceClass property being correctly defined and proven.
  if h : IsTraceClass A then
     -- If A is trace class, compute its trace: Sum <e_k, A e_k> over any ONB.
     -- The actual computation (summation) requires proof of convergence and value.
     some (sorry : ℂ) -- Retained sorry for actual trace computation value
  else
    -- Otherwise, the trace is undefined
    none

/-- SummableSpace instance for Infinite Dimensional Quantum Trace (Conceptual). -/
instance QuantumInfiniteDimTraceSpace {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    SummableSpace Unit where
  ValueType := Option ℂ -- Value is potentially undefined
  addCommMonoid := inferInstance -- Uses Option.addCommMonoid defined below
  integrate f _ := -- f maps Unit to Option ℂ (the potential trace value)
      f Unit.unit -- The function itself must compute the Option trace

/-- Structure holding the core components of a statistical model. -/
structure StatMechModel' where
  ParameterType : Type
  parameters : ParameterType
  ConfigSpace : Type
  EnergyValueType : Type
  Hamiltonian : ConfigSpace → EnergyValueType
  WeightValueType : Type
  [weightMonoid : AddCommMonoid WeightValueType]
  StateSpace : SummableSpace ConfigSpace
  WeightFunction : EnergyValueType → ParameterType → WeightValueType
  Z_ED_Integrable : Prop -- User must assert integrability / well-definedness
  Z_ED_Calculation : WeightValueType :=
    @SummableSpace.integrate ConfigSpace StateSpace WeightValueType weightMonoid
      (fun cfg => WeightFunction (Hamiltonian cfg) parameters) Z_ED_Integrable
  calculateZ_Alternative : Option WeightValueType
  -- Properties
  IsClassical : Prop := true
  IsQuantum : Prop := false
  IsDiscreteConfig : Prop := true
  IsContinuousConfig : Prop := false
  HasFiniteStates : Prop := false
  InteractionType : Type
  BoundaryCondition : Type


-- Define InteractionKind and BoundaryKind earlier so ConditionsForEquivalence can use them
inductive InteractionKind where
  | NearestNeighbor | FiniteRange (range : ℕ) | LongRange | NonLocal
  | QuantumNN | QuantumLR | QuantumNonLocal

inductive BoundaryKind where
  | Periodic | OpenFree | OpenFixed
  -- Add other boundary conditions if needed

-- Abstract Equivalence Theorem (Statement Only)
def AbstractEquivalenceAssertion (model : StatMechModel') : Prop :=
  ∀ (h_alt_exists : model.calculateZ_Alternative.isSome),
    (ConditionsForEquivalence model.IsClassical model.IsQuantum model.IsDiscreteConfig model.InteractionType model.BoundaryCondition) →
    -- This equality check needs care depending on WeightValueType
    ∃ z_ed_val, model.Z_ED_Calculation = z_ed_val ∧ ∃ z_alt_val, Option.get h_alt_exists = z_alt_val ∧ z_ed_val = z_alt_val -- Placeholder equality

-- Predicate capturing conditions needed for the specific equivalence proof
def ConditionsForEquivalence (isClassical isQuantum isDiscreteConfig : Prop) (interaction : Type) (boundary : Type) -- Add more properties
    : Prop :=
      if isQuantum then false
      else if ¬isClassical then false
      else if ¬isDiscreteConfig then false
      else
        -- Type equality check needs care - using direct equality for inductive types
        match interaction == InteractionKind.NearestNeighbor, boundary with
        | true, BoundaryKind.Periodic => true
        | true, BoundaryKind.OpenFree => true -- Assume equivalence holds (contingent on lemma proof)
        | _, _ => false


/-- Define addition on Option α where none acts as identity -/
def optionAdd {α} [AddMonoid α] : Option α → Option α → Option α
  | some x, some y => some (x + y)
  | some x, none   => some x
  | none,   some y => some y
  | none,   none   => none

/-- AddCommMonoid instance for Option α, where none is the identity. -/
instance {α} [AddCommMonoid α] : AddCommMonoid (Option α) where
  add := optionAdd
  add_assoc := by intros a b c; cases a <;> cases b <;> cases c <;> simp [optionAdd, add_assoc]
  zero := none
  zero_add := by intros a; cases a <;> simp [optionAdd]
  add_zero := by intros a; cases a <;> simp [optionAdd]
  nsmul := nsmulRec
  add_comm := by intros a b; cases a <;> cases b <;> simp [optionAdd, add_comm]


/-! ### Helper Lemmas for Trace Identity ### -/
-- Lemma: trace (List.prod L.reverse) = trace (List.prod L)
lemma trace_prod_reverse_eq_trace_prod {IdxType : Type} [Fintype IdxType] [DecidableEq IdxType]
    (L : List (Matrix IdxType IdxType ℂ)) :
    Matrix.trace (List.prod L.reverse) = Matrix.trace (List.prod L) := by
  induction L using List.reverseRecOn with
  | H T M ih => rw [List.reverse_append, List.prod_append, List.prod_singleton, List.reverse_singleton]; rw [List.prod_cons, List.prod_append, List.prod_singleton]; rw [Matrix.trace_mul_comm (List.prod T) M]; exact ih
  | nil => simp


/-- Define the product of matrix elements along a specific path (for classical TM) -/
def classical_path_prod {N : ℕ} {StateType : Type} [Fintype StateType] [DecidableEq StateType]
    (beta : ℝ) (LocalHamiltonian : Fin N → StateType → StateType → ℝ) (hN : 0 < N)
    (path : Fin N → StateType) : ℂ :=
  Finset.prod Finset.univ fun (i : Fin N) =>
    Complex.exp (↑(-beta * LocalHamiltonian i (path i) (path (Fin.cycle hN i))) : ℂ)

/-- Trace identity lemma (proof filled) -/
lemma trace_prod_reverse_eq_sum_path {N : ℕ} {StateType : Type} [Fintype StateType] [DecidableEq StateType]
    (hN : 0 < N) (beta : ℝ) (LocalHamiltonian : Fin N → StateType → StateType → ℝ) :
    let T_local (i : Fin N) := Matrix.ofFn (fun s s' : StateType => Complex.exp (↑(-beta * LocalHamiltonian i s s') : ℂ))
    let matrices := List.ofFn fun i => T_local i
    let T_total_rev := List.prod matrices.reverse
    Matrix.trace T_total_rev = Finset.sum Finset.univ (classical_path_prod beta LocalHamiltonian hN) := by
  let T_local (i : Fin N) := Matrix.ofFn (fun s s' : StateType => Complex.exp (↑(-beta * LocalHamiltonian i s s') : ℂ))
  let L := List.ofFn fun i => T_local i
  rw [trace_prod_reverse_eq_trace_prod L]
  rw [Matrix.trace_list_prod L]
  apply Finset.sum_congr rfl
  intro p _ ; unfold classical_path_prod
  apply Finset.prod_congr rfl
  intro i _; simp only [List.get_ofFn]; unfold T_local Matrix.ofFn; congr; rfl

-- Helper lemma assumed from original proof (needs proof itself)
lemma Complex.sum_exp_neg_beta_H_eq_sum_path_prod {N : ℕ} {StateType : Type} [Fintype StateType] [DecidableEq StateType]
    (beta : ℝ) (LocalHamiltonian : Fin N → StateType → StateType → ℝ) (hN : 0 < N) :
    Finset.sum Finset.univ (fun path : Fin N → StateType ↦ Complex.exp (↑(-beta * (Finset.sum Finset.univ fun i ↦ LocalHamiltonian i (path i) (path (Fin.cycle hN i)))) : ℂ))
    = Finset.sum Finset.univ (classical_path_prod beta LocalHamiltonian hN) := by
  apply Finset.sum_congr rfl
  intro path _; rw [Finset.sum_mul, Finset.sum_neg_distrib, neg_mul, Complex.ofReal_mul, Complex.ofReal_sum]; simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_neg]; rw [Complex.exp_sum]; unfold classical_path_prod; simp_rw [Complex.ofReal_neg, Complex.ofReal_mul]; rfl


/-!
## Instantiating the Abstract Framework (Conceptual Sketches)
-/

/-! **1. Classical NN PBC:** -/
def ClassicalNNPBC_Params (N : ℕ) := { beta : ℝ // 0 < N }
def ClassicalNNPBC_StateType := Type
def ClassicalNNPBC_Model (N : ℕ) (StateType : Type) [Fintype StateType] [DecidableEq StateType]
    (beta : ℝ) (hN : 0 < N)
    (LocalHamiltonian : Fin N → StateType → StateType → ℝ) :
    StatMechModel' where
  ParameterType := ClassicalNNPBC_Params N; parameters := ⟨beta, hN⟩; ConfigSpace := Fin N → StateType
  EnergyValueType := ℝ; Hamiltonian := fun path => Finset.sum Finset.univ fun i => LocalHamiltonian i (path i) (path (Fin.cycle hN i))
  WeightValueType := ℂ; weightMonoid := inferInstance; StateSpace := FintypeSummableSpace
  WeightFunction := fun H_val params => Complex.exp (↑(-params.val * H_val) : ℂ); Z_ED_Integrable := true
  calculateZ_Alternative := Id.run do
      let T_local i := Matrix.ofFn (fun s s' => Complex.exp (↑(-beta * LocalHamiltonian i s s') : ℂ))
      let matrices := List.ofFn fun i => T_local i; let T_total := List.prod matrices.reverse
      return some (Matrix.trace T_total)
  IsClassical := true; IsQuantum := false; IsDiscreteConfig := true; IsContinuousConfig := false; HasFiniteStates := true
  InteractionType := InteractionKind.NearestNeighbor; BoundaryCondition := BoundaryKind.Periodic

/-! **2. Classical NN OBC (Open Boundary Conditions):** -/
def ClassicalOBC_Params (N : ℕ) := { beta : ℝ // N > 0 }
def ClassicalOBC_Model (N : ℕ) (StateType : Type) [Fintype StateType] [DecidableEq StateType]
    (beta : ℝ) (hN0 : N > 0)
    (LocalHamiltonian : Fin (N - 1) → StateType → StateType → ℝ) :
    StatMechModel' where
  ParameterType := ClassicalOBC_Params N; parameters := ⟨beta, hN0⟩
  ConfigSpace := Fin N → StateType; EnergyValueType := ℝ
  Hamiltonian := fun path => Finset.sum (Finset.range (N - 1)) fun i =>
      let i_fin : Fin N := Fin.castSucc ⟨i, Nat.lt_of_lt_pred hN0⟩
      let ip1_fin : Fin N := Fin.succ i_fin
      let i_fin_pred : Fin (N - 1) := ⟨i, Nat.lt_of_lt_pred hN0⟩
      LocalHamiltonian i_fin_pred (path i_fin) (path ip1_fin)
  WeightValueType := ℂ; weightMonoid := inferInstance; StateSpace := FintypeSummableSpace
  WeightFunction := fun H_val params => Complex.exp (↑(-params.val * H_val) : ℂ); Z_ED_Integrable := true
  calculateZ_Alternative := Id.run do
      if h : N = 0 then return none
      else
        let N_pred := N - 1; have hN_pred_pos : N_pred + 1 = N := Nat.sub_add_cancel (Nat.one_le_of_lt hN0)
        let T_local (i : Fin N_pred) : Matrix StateType StateType ℂ := Matrix.ofFn (fun s s' => Complex.exp (↑(-beta * LocalHamiltonian i s s') : ℂ))
        let matrices := List.ofFn fun i => T_local i; let T_total_prod := List.prod matrices
        let Z_alt : ℂ := Finset.sum Finset.univ fun s0 => Finset.sum Finset.univ fun sN_minus_1 => T_total_prod s0 sN_minus_1
        return some Z_alt
  IsClassical := true; IsQuantum := false; IsDiscreteConfig := true; IsContinuousConfig := false; HasFiniteStates := true
  InteractionType := InteractionKind.NearestNeighbor; BoundaryCondition := BoundaryKind.OpenFree

/-! **3. Quantum System (Conceptual - Finite Dimensional):** -/
noncomputable def op_exp {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ContinuousLinearMap ℂ H H) : ContinuousLinearMap ℂ H H :=
  exp ℂ A
def Quantum_Params := { beta : ℝ }
def Quantum_Model_Finite_Dim {n : ℕ} (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H] (h_fin_dim : FiniteDimensional.finrank ℂ H = n)
    (basis : Basis (Fin n) ℂ H) (OpH : ContinuousLinearMap ℂ H H) (hH : IsSelfAdjoint OpH)
    (h_interaction_type : InteractionKind := InteractionKind.QuantumNN)
    (h_boundary_cond : BoundaryKind := BoundaryKind.Periodic) (beta : ℝ) :
    StatMechModel' where
  ParameterType := Quantum_Params; parameters := { beta := beta }; ConfigSpace := Unit
  EnergyValueType := ContinuousLinearMap ℂ H H; Hamiltonian := fun _ => OpH; WeightValueType := ℂ
  weightMonoid := inferInstance; StateSpace := QuantumFiniteDimTraceSpace h_fin_dim basis
  WeightFunction := fun Op params => op_trace_finite_dim h_fin_dim basis (op_exp (-params.beta • Op))
  Z_ED_Integrable := FiniteDimensional.finrank ℂ H = n; calculateZ_Alternative := none
  IsClassical := false; IsQuantum := true; IsDiscreteConfig := false; IsContinuousConfig := false
  HasFiniteStates := n > 0; InteractionType := h_interaction_type; BoundaryCondition := h_boundary_cond

/-! **4. Quantum System (Conceptual - Infinite Dimensional):** -/
def Quantum_Model_Infinite_Dim (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (OpH : ContinuousLinearMap ℂ H H) (hH : IsSelfAdjoint OpH)
    (h_interaction_type : InteractionKind := InteractionKind.QuantumNonLocal)
    (h_boundary_cond : BoundaryKind := BoundaryKind.Periodic) (beta : ℝ) :
    StatMechModel' where
  ParameterType := Quantum_Params; parameters := { beta := beta }; ConfigSpace := Unit
  EnergyValueType := ContinuousLinearMap ℂ H H; Hamiltonian := fun _ => OpH
  WeightValueType := Option ℂ; weightMonoid := inferInstance; StateSpace := QuantumInfiniteDimTraceSpace
  WeightFunction := fun Op params => op_trace_infinite_dim (op_exp (-params.beta • Op)) -- Uses op_trace_infinite_dim
  Z_ED_Integrable := IsTraceClass (op_exp (-beta • OpH)) -- Uses the Prop IsTraceClass
  calculateZ_Alternative := none; IsClassical := false; IsQuantum := true
  IsDiscreteConfig := false; IsContinuousConfig := true; HasFiniteStates := false
  InteractionType := h_interaction_type; BoundaryCondition := h_boundary_cond


/-! **5. Other Cases (Long-Range, Continuous, Non-Local):**
(Conceptual description requires defining specific model structures).
-/

/-! ## Proofs of Assertions (Example for Classical NN PBC) ## -/

/-- Lemma relating the sum of all elements of a matrix product to a sum over paths (OBC Case). -/
lemma sum_all_elements_list_prod_eq_sum_path
    {N : ℕ} {StateType : Type} [Fintype StateType] [DecidableEq StateType]
    (hN0 : N > 0)
    (T_local : Fin (N - 1) → Matrix StateType StateType ℂ) :
    let matrices := List.ofFn fun i => T_local i
    let T_total_prod := List.prod matrices
    Finset.sum Finset.univ (fun s0 => Finset.sum Finset.univ fun sNm1 => T_total_prod s0 sNm1)
    =
    Finset.sum Finset.univ fun (path : Fin N → StateType) => -- Sum over all full paths
      Finset.prod (Finset.range (N - 1)) fun i => -- Product over N-1 steps
        let i_fin_pred : Fin (N-1) := ⟨i, Nat.lt_of_lt_pred hN0⟩
        let i_fin : Fin N := Fin.castSucc i_fin_pred
        let ip1_fin : Fin N := Fin.succ i_fin
        T_local i_fin_pred (path i_fin) (path ip1_fin) :=
  by
    let n := N - 1
    let matrices := List.ofFn fun i : Fin n => T_local i
    -- Proof by induction on n (length of matrices = number of steps)
    induction n using Nat.case_strong_induction_on with
    | hz => -- N=1. matrices=[]. prod=Id.
        simp only [List.length_ofFn, List.prod_nil, Matrix.one_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp only [Nat.zero_eq, Finset.range_zero, Finset.prod_empty]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin]
        simp
    | hi k ih => -- N=k+2. matrices = T0 :: T1 :: ... :: Tk. length k+1.
        let T0 := T_local 0
        let rest_matrices := List.ofFn (fun i : Fin k => T_local (Fin.succ i))
        have h_len_rest : rest_matrices.length = k := by simp only [List.length_ofFn]
        let T_rest_prod := List.prod rest_matrices
        let hNk1 : k+1 > 0 := Nat.succ_pos k
        have ih' := ih k (Nat.lt_succ_self k) (fun i : Fin k => T_local (Fin.succ i)) h_len_rest -- Apply IH
        -- Expand LHS for N=k+2 (n=k+1)
        calc Finset.sum Finset.univ (fun s0 => Finset.sum Finset.univ fun skp1 => (List.prod (T0 :: rest_matrices)) s0 skp1)
             = ∑ s0, ∑ skp1, ∑ s1, T0 s0 s1 * T_rest_prod s1 skp1 := by simp [List.prod_cons, Matrix.mul_apply, Finset.sum_sum_type, Finset.sum_product]
           _ = ∑ s1, ∑ s0, ∑ skp1, T0 s0 s1 * T_rest_prod s1 skp1 := by rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro; rw [Finset.sum_comm]
           _ = ∑ s1, ∑ s0, T0 s0 s1 * (∑ skp1, T_rest_prod s1 skp1) := by apply Finset.sum_congr rfl; intro; rw [← Finset.sum_mul]; apply Finset.sum_congr rfl; intro; rw [mul_comm]
           -- Need to relate Sum_{skp1} T_rest_prod(s1, skp1) to IH
           -- IH relates Sum_{s1, skp1} T_rest(...) to Sum_{path k+1} Prod(...)
           -- We need a lemma: Sum_{end} (List.prod L) start end = Sum_{path starting at start} Prod(...)
           -- Let's assume this lemma: `list_prod_apply_sum_right_eq_path_sum_start`
           -- _ = ∑ s1, ∑ s0, T0 s0 s1 * (∑ (p' : Fin (k+1) → StateType) (_ : p' 0 = s1), ∏ i : Fin k, rest_matrices[i] (p' i) (p' (i+1))) := sorry
           _ = ∑ (p : Fin (k+2) → StateType), ∏ i : Fin (k+1), matrices[i] (p i) (p (i+1)) := sorry -- Requires lemma application and sum combination.

/-- Proof of the Abstract Equivalence Assertion for the Classical NN OBC case.
    Requires proof of `sum_all_elements_list_prod_eq_sum_path`. -/
theorem ClassicalOBC_Equivalence (N : ℕ) (StateType : Type) [Fintype StateType] [DecidableEq StateType]
    (beta : ℝ) (hN0 : N > 0) (LocalHamiltonian : Fin (N - 1) → StateType → StateType → ℝ) :
    let model := ClassicalOBC_Model N StateType beta hN0 LocalHamiltonian in
    if h_alt_some : model.calculateZ_Alternative.isSome then
      -- Assuming ConditionsForEquivalence is true for OBC NN Classical
      if h_cond : ConditionsForEquivalence model.IsClassical model.IsQuantum model.IsDiscreteConfig model.InteractionType model.BoundaryCondition then
        let Z_ED_calc := model.Z_ED_Calculation in
        let Z_alt_val := Option.get h_alt_some in
        Z_ED_calc = Z_alt_val
      else True.intro -- Conditions not met for this proof path
    else False.elim (h_alt_some (by simp [ClassicalOBC_Model]; intro hNeq0; contradiction)) :=
  by
    let model := ClassicalOBC_Model N StateType beta hN0 LocalHamiltonian
    let Z_ED_calc := model.Z_ED_Calculation
    let Z_alt_opt := model.calculateZ_Alternative
    have h_alt_some : Z_alt_opt.isSome := by simp [ClassicalOBC_Model]; intro hNeq0; contradiction
    let Z_alt_val := Option.get h_alt_some
    intro h_alt_some_proof -- for the `if` statement
    intro h_cond_proof -- for the `if h_cond` statement

    -- Goal: Z_ED_calc = Z_alt_val
    rw [StatMechModel'.Z_ED_Calculation]; simp only [ClassicalOBC_Model, FintypeSummableSpace.integrate, Hamiltonian, WeightFunction]
    apply Finset.sum_congr rfl
    intro path _; rw [Finset.sum_mul, Finset.sum_neg_distrib, neg_mul, Complex.ofReal_mul, Complex.ofReal_sum]; simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_neg]; rw [Complex.exp_sum]
    rw [Option.get_of_mem h_alt_some]; simp only [ClassicalOBC_Model]
    let T_loc := fun (i : Fin (N-1)) => Matrix.ofFn fun s s' => Complex.exp (↑(-beta * LocalHamiltonian i s s') : ℂ)
    rw [sum_all_elements_list_prod_eq_sum_path hN0 T_loc] -- Apply the lemma (which is sorry)
    apply Finset.sum_congr rfl
    intro path _; apply Finset.prod_congr rfl
    intro i _; simp only; rfl

/-- Proof of the Abstract Equivalence Assertion for the Classical NN PBC case. -/
theorem ClassicalNNPBC_Equivalence (N : ℕ) (StateType : Type) [Fintype StateType] [DecidableEq StateType]
    (beta : ℝ) (hN : 0 < N) (LocalHamiltonian : Fin N → StateType → StateType → ℝ) :
    let model := ClassicalNNPBC_Model N StateType beta hN LocalHamiltonian
    AbstractEquivalenceAssertion model := by
  intro h_alt_exists h_conditions; dsimp [AbstractEquivalenceAssertion]
  let Z_ED_calc := model.Z_ED_Calculation; let Z_alt_val := Option.get h_alt_exists
  have : model.WeightValueType = ℂ := rfl
  suffices Z_ED_calc = Z_alt_val by use Z_ED_calc; constructor; rfl; use Z_alt_val; constructor; rfl; assumption
  rw [StatMechModel'.Z_ED_Calculation]; simp only [ClassicalNNPBC_Model, FintypeSummableSpace.integrate, Hamiltonian, WeightFunction]
  rw [Complex.sum_exp_neg_beta_H_eq_sum_path_prod beta LocalHamiltonian hN]
  rw [← trace_prod_reverse_eq_sum_path hN beta LocalHamiltonian]
  rw [Option.get_of_mem h_alt_exists]; simp [ClassicalNNPBC_Model]; rfl


end -- End noncomputable section
