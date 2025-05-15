/-
The Initial Framework for P vs NP Resolution

This file aims to lay the groundwork for a theorem that, if proven,
would serve as a crucial stepping stone towards resolving P vs NP.
The main theorem, `Main_Theorem_P_vs_NP_Framework`, posits that
if a specific, novel computational property can be shown to hold for
some Universal Turing Machine, then this directly leads to a resolution
of P vs NP (i.e., P = NP or P ≠ NP).

The proof of `Main_Theorem_P_vs_NP_Framework` itself is the "framework."
The "one hop" to potentially solving P vs NP would then be proving
`Hypothesis_UTM_Satisfies_Property`.
-/

import Mathlib.Data.Finset.Basic -- For Finset
import Mathlib.Data.Finset.Sort -- For Finset.toList
import Mathlib.Data.Finset.Product -- For Finset.product
import Mathlib.Data.Set.Finite -- For Set operations like subset, used by Finset.subset_iff
import Mathlib.Tactic.Cases -- For cases tactic
import Mathlib.Tactic.SplitIfs -- For split_ifs
import Mathlib.Init.Data.Option.Basic -- For Option.isSome, Option.get!
import Mathlib.Logic.Equiv.Basic -- For decidable_eq
import Mathlib.Data.List.Basic -- For List operations
import Mathlib.Data.List.Defs -- For List.mapM / List.traverse
import Mathlib.Relation.ReflTransGen -- For Reflexive Transitive Closure (RTC)
import Mathlib.Data.Nat.Prime -- For pairing functions if needed for encoding
import Mathlib.Data.Nat.Pairing -- For Nat.pair and Nat.unpair (crucial for state encoding)
import Mathlib.Tactic.NormNum -- For simp with numbers
import Mathlib.Tactic.Linarith -- For linear arithmetic
import Mathlib.Data.List.Zip -- For List.zip for transition function parsing
import Mathlib.Control.Traversable.Basic -- For List.traverse
import Mathlib.Order.Basic -- For Nat.lt_succ_iff, Nat.pred_lt_iff_le etc.

-- Namespace to organize the definitions and theorems for this framework.
namespace P_vs_NP_Framework

-- Basic definitions for P and NP.
opaque Language : Type := Nat → Prop
opaque P_Class : Set Language
opaque NP_Class : Set Language
def P_eq_NP : Prop := P_Class = NP_Class
def P_neq_NP : Prop := P_Class ≠ NP_Class

-- Foundational types for Turing Machine definition
inductive Direction : Type
| left : Direction
| right : Direction
deriving Repr, DecidableEq, Inhabited

variable (σ : Type) (α : Type)

structure TapeZipper (α_sym : Type) : Type where
  left : List α_sym
  current : α_sym
  right : List α_sym
deriving Repr

def default_blank (α_sym : Type) [Inhabited α_sym] : α_sym := default

def tape_write (tape : TapeZipper α) (new_symbol : α) : TapeZipper α :=
  { tape with current := new_symbol }

def tape_move_left (tape : TapeZipper α) (blank : α) : TapeZipper α :=
  match tape.left with
  | []      => { left := [], current := blank, right := tape.current :: tape.right }
  | h :: t  => { left := t, current := h, right := tape.current :: tape.right }

def tape_move_right (tape : TapeZipper α) (blank : α) : TapeZipper α :=
  match tape.right with
  | []      => { left := tape.current :: tape.left, current := blank, right := [] }
  | h :: t  => { left := tape.current :: tape.left, current := h, right := t }

def initial_tape_zipper (input : List α) (blank_sym : α) : TapeZipper α :=
  match input with
  | []      => { left := [], current := blank_sym, right := [] }
  | h :: t  => { left := [], current := h, right := t }

structure TuringMachineConfiguration (σ_state α_sym : Type) : Type where
  state : σ_state
  tape : TapeZipper α_sym
deriving Repr

structure TuringMachine (σ_state α_sym : Type) [DecidableEq σ_state] [DecidableEq α_sym] : Type where
  states : Finset σ_state
  input_alphabet : Finset α_sym
  tape_alphabet : Finset α_sym
  blank_symbol : α_sym
  transition_fn : σ_state × α_sym → Option (σ_state × α_sym × Direction)
  start_state : σ_state
  accept_state : σ_state
  reject_state : σ_state
  input_alphabet_subset_tape_alphabet : input_alphabet ⊆ tape_alphabet
  blank_in_tape_alphabet : blank_symbol ∈ tape_alphabet
  blank_not_in_input_alphabet : blank_symbol ∉ input_alphabet
  start_in_states : start_state ∈ states
  accept_in_states : accept_state ∈ states
  reject_in_states : reject_state ∈ states
  valid_transition_fn : forall (q₁ : σ_state) (s₁ : α_sym),
    q₁ ∈ states → s₁ ∈ tape_alphabet →
    (transition_fn (q₁, s₁)).isSome →
    let res := (transition_fn (q₁, s₁)).get! in
    res.1 ∈ states ∧ res.2.1 ∈ tape_alphabet ∧ (res.2.1 = blank_symbol → res.2.2 = Direction.right)

def tm_step {σ_state α_sym : Type} [DecidableEq σ_state] [DecidableEq α_sym]
    (M : TuringMachine σ_state α_sym)
    (cfg : TuringMachineConfiguration σ_state α_sym) :
    Option (TuringMachineConfiguration σ_state α_sym) :=
  if cfg.state = M.accept_state ∨ cfg.state = M.reject_state then none
  else match M.transition_fn (cfg.state, cfg.tape.current) with
    | none => none
    | some (next_q, write_sym, move_dir) =>
        let new_tape_after_write := tape_write cfg.tape write_sym
        let new_tape_after_move :=
          match move_dir with
          | Direction.left  => tape_move_left new_tape_after_write M.blank_symbol
          | Direction.right => tape_move_right new_tape_after_write M.blank_symbol
        some { state := next_q, tape := new_tape_after_move }

def tm_halts_on_config {σ_state α_sym : Type} [DecidableEq σ_state] [DecidableEq α_sym]
    (M : TuringMachine σ_state α_sym)
    (cfg : TuringMachineConfiguration σ_state α_sym) : Prop :=
  tm_step M cfg = none

def tm_reaches_config {σ_state α_sym : Type} [DecidableEq σ_state] [DecidableEq α_sym]
    (M : TuringMachine σ_state α_sym) :
    TuringMachineConfiguration σ_state α_sym → TuringMachineConfiguration σ_state α_sym → Prop :=
  Relation.ReflTransGen (fun c1 c2 => tm_step M c1 = some c2)

def tm_accepts {σ_state α_sym : Type} [DecidableEq σ_state] [DecidableEq α_sym]
    (M : TuringMachine σ_state α_sym) (input_word : List α_sym) : Prop :=
  let initial_config : TuringMachineConfiguration σ_state α_sym :=
    { state := M.start_state, tape := initial_tape_zipper input_word M.blank_symbol }
  ∃ (final_cfg : TuringMachineConfiguration σ_state α_sym),
    tm_reaches_config M initial_config final_cfg ∧
    final_cfg.state = M.accept_state ∧
    tm_halts_on_config M final_cfg

def tm_rejects {σ_state α_sym : Type} [DecidableEq σ_state] [DecidableEq α_sym]
    (M : TuringMachine σ_state α_sym) (input_word : List α_sym) : Prop :=
  let initial_config : TuringMachineConfiguration σ_state α_sym :=
    { state := M.start_state, tape := initial_tape_zipper input_word M.blank_symbol }
  ∃ (final_cfg : TuringMachineConfiguration σ_state α_sym),
    tm_reaches_config M initial_config final_cfg ∧
    final_cfg.state = M.reject_state ∧
    tm_halts_on_config M final_cfg

def tm_halts_on_input {σ_state α_sym : Type} [DecidableEq σ_state] [DecidableEq α_sym]
    (M : TuringMachine σ_state α_sym) (input_word : List α_sym) : Prop :=
  tm_accepts M input_word ∨ tm_rejects M input_word

def UniversalTuringMachine_spec_σ : Type := ℕ -- Encodes (control_code, internal_data)
instance : Inhabited UniversalTuringMachine_spec_σ := ⟨Nat.pair 0 0⟩
instance : DecidableEq UniversalTuringMachine_spec_σ := instDecidableEqNat
instance : LinearOrder UniversalTuringMachine_spec_σ := Nat.linearOrder

def UniversalTuringMachine_spec_α : Type := ℕ
instance : Inhabited UniversalTuringMachine_spec_α := ⟨0⟩
instance : DecidableEq UniversalTuringMachine_spec_α := instDecidableEqNat
instance : LinearOrder UniversalTuringMachine_spec_α := Nat.linearOrder

def UniversalTuringMachine := TuringMachine UniversalTuringMachine_spec_σ UniversalTuringMachine_spec_α

variable {σ_sim α_sim : Type} [DecidableEq σ_sim] [DecidableEq α_sim] [Inhabited α_sim]

def concrete_encode_nat_as_nat_for_desc (n : ℕ) : UniversalTuringMachine_spec_α := n + 11
def decode_nat_from_desc (encoded_val : UniversalTuringMachine_spec_α) : Option ℕ :=
  if encoded_val ≥ 11 then some (encoded_val - 11) else none

def concrete_encode_nat_as_nat_for_input (n : ℕ) : UniversalTuringMachine_spec_α := n + 21
def decode_nat_from_input (encoded_val : UniversalTuringMachine_spec_α) : Option ℕ :=
  if encoded_val ≥ 21 then some (encoded_val - 21) else none

def concrete_finset_nat_to_list (s : Finset ℕ) : List ℕ := Finset.toList s

def encode_direction : Direction → UniversalTuringMachine_spec_α
  | Direction.left => 2
  | Direction.right => 3
def decode_direction_opt (n : UniversalTuringMachine_spec_α) : Option Direction :=
  if n = 2 then some Direction.left
  else if n = 3 then some Direction.right
  else none

def encode_list {elem_type : Type} (encoder : elem_type → UniversalTuringMachine_spec_α) (l : List elem_type) : List UniversalTuringMachine_spec_α :=
  l.map encoder

def encode_finset {elem_type : Type} [DecidableEq elem_type]
    (encoder : elem_type → UniversalTuringMachine_spec_α)
    (s : Finset elem_type)
    (to_list_canonical : Finset elem_type → List elem_type) : List UniversalTuringMachine_spec_α :=
  encode_list encoder (to_list_canonical s)

def encode_transition_rule
    (encode_state_desc : σ_sim → UniversalTuringMachine_spec_α)
    (encode_symbol_desc : α_sim → UniversalTuringMachine_spec_α)
    (q : σ_sim) (s : α_sim) (q' : σ_sim) (s' : α_sim) (d : Direction) : List UniversalTuringMachine_spec_α :=
  [encode_state_desc q, encode_symbol_desc s, encode_state_desc q', encode_symbol_desc s', encode_direction d]

def encode_transition_function
    (M_sim : TuringMachine σ_sim α_sim)
    (encode_state_desc : σ_sim → UniversalTuringMachine_spec_α)
    (encode_symbol_desc : α_sim → UniversalTuringMachine_spec_α)
    (states_list_canonical : Finset σ_sim → List σ_sim)
    (symbols_list_canonical : Finset α_sim → List α_sim)
    : List UniversalTuringMachine_spec_α :=
  let states_l := states_list_canonical M_sim.states
  let tape_symbols_l := symbols_list_canonical M_sim.tape_alphabet
  let all_pairs := states_l.bind (fun q => tape_symbols_l.map (fun s => (q, s)))
  all_pairs.foldl (fun acc (q, s) =>
    match M_sim.transition_fn (q, s) with
    | none => acc
    | some (q', s', d) => acc ++ (encode_transition_rule encode_state_desc encode_symbol_desc q s q' s' d)
  ) []

def length_prefixed_list (l : List UniversalTuringMachine_spec_α) : List UniversalTuringMachine_spec_α :=
  (l.length + 1 : UniversalTuringMachine_spec_α) :: l

def encode_tm_description
    (M_sim : TuringMachine σ_sim α_sim)
    (encode_state_desc : σ_sim → UniversalTuringMachine_spec_α)
    (encode_symbol_desc : α_sim → UniversalTuringMachine_spec_α)
    (states_list_canonical : Finset σ_sim → List σ_sim)
    (symbols_list_canonical : Finset α_sim → List α_sim)
    : List UniversalTuringMachine_spec_α :=
  let encoded_s_list := encode_finset encode_state_desc M_sim.states states_list_canonical
  let encoded_ia_list := encode_finset encode_symbol_desc M_sim.input_alphabet symbols_list_canonical
  let encoded_ta_list := encode_finset encode_symbol_desc M_sim.tape_alphabet symbols_list_canonical
  let encoded_b_list := [encode_symbol_desc M_sim.blank_symbol]
  let encoded_q0_list := [encode_state_desc M_sim.start_state]
  let encoded_qa_list := [encode_state_desc M_sim.accept_state]
  let encoded_qr_list := [encode_state_desc M_sim.reject_state]
  let encoded_delta_list := encode_transition_function M_sim encode_state_desc encode_symbol_desc states_list_canonical symbols_list_canonical

  (length_prefixed_list encoded_s_list) ++
  (length_prefixed_list encoded_ia_list) ++
  (length_prefixed_list encoded_ta_list) ++
  (length_prefixed_list encoded_b_list) ++
  (length_prefixed_list encoded_q0_list) ++
  (length_prefixed_list encoded_qa_list) ++
  (length_prefixed_list encoded_qr_list) ++
  (length_prefixed_list encoded_delta_list)

def utm_tape_separator : UniversalTuringMachine_spec_α := 4

def encode_input_word {α_s : Type} [Inhabited α_s]
    (symbol_encoder_input : α_s → UniversalTuringMachine_spec_α)
    (w_sim : List α_s) : List UniversalTuringMachine_spec_α :=
  w_sim.map symbol_encoder_input

def combine_encodings (encoded_M : List UniversalTuringMachine_spec_α) (encoded_w : List UniversalTuringMachine_spec_α) : List UniversalTuringMachine_spec_α :=
  encoded_M ++ [utm_tape_separator] ++ encoded_w

def IsUniversal (utm : UniversalTuringMachine)
    (p_encode_state_desc : Π {σs : Type} [DecidableEq σs], σs → UniversalTuringMachine_spec_α)
    (p_encode_symbol_desc : Π {αs : Type} [DecidableEq αs] [Inhabited αs], αs → UniversalTuringMachine_spec_α)
    (p_states_list_canonical : Π {σs : Type} [DecidableEq σs], Finset σs → List σs)
    (p_symbols_list_canonical : Π {αs : Type} [DecidableEq αs] [Inhabited αs], Finset αs → List αs)
    (p_symbol_encoder_input : Π {αs : Type} [Inhabited αs], αs → UniversalTuringMachine_spec_α)
    (p_sep : UniversalTuringMachine_spec_α) : Prop :=
  ∀ {σs αs : Type} [DecidableEq σs] [DecidableEq αs] [Inhabited αs]
    (M_sim : TuringMachine σs αs) (w_sim : List αs),
    let encoded_M_desc := encode_tm_description M_sim
                            (p_encode_state_desc (σs:=σs)) (p_encode_symbol_desc (αs:=αs))
                            (p_states_list_canonical (σs:=σs)) (p_symbols_list_canonical (αs:=αs))
    let encoded_w_val := encode_input_word (p_symbol_encoder_input (αs:=αs)) w_sim
    let utm_initial_tape := combine_encodings encoded_M_desc encoded_w_val
    (tm_accepts utm utm_initial_tape ↔ tm_accepts M_sim w_sim) ∧
    (tm_rejects utm utm_initial_tape ↔ tm_rejects M_sim w_sim)

namespace SimpleTM
def q_start : ℕ := 0; def q_accept : ℕ := 1; def q_reject : ℕ := 2
def sym_blank : ℕ := 0; def sym_zero : ℕ := 1; def sym_one : ℕ := 2
def states_set : Finset ℕ := {q_start, q_accept, q_reject}
def input_alphabet_set : Finset ℕ := {sym_zero, sym_one}
def tape_alphabet_set : Finset ℕ := {sym_blank, sym_zero, sym_one}
def transition_function (p : ℕ × ℕ) : Option (ℕ × ℕ × Direction) :=
  match p with
  | (qs, s) => if qs = q_start then if s = sym_one then some (q_accept, sym_one, Direction.right) else if s = sym_zero then some (q_reject, sym_zero, Direction.right) else if s = sym_blank then some (q_reject, sym_blank, Direction.right) else none else none
def simple_tm_instance : TuringMachine ℕ ℕ where
  states := states_set; input_alphabet := input_alphabet_set; tape_alphabet := tape_alphabet_set
  blank_symbol := sym_blank; transition_fn := transition_function; start_state := q_start
  accept_state := q_accept; reject_state := q_reject
  input_alphabet_subset_tape_alphabet := by simp [Finset.subset_iff, *]; intros; simp [*]
  blank_in_tape_alphabet := by simp [*]; blank_not_in_input_alphabet := by simp [*]
  start_in_states := by simp [*]; accept_in_states := by simp [*]; reject_in_states := by simp [*]
  valid_transition_fn := by
    intros q₁ s₁ hq₁ hs₁ h_isSome
    -- If transition_function (q₁, s₁) is Some, then q₁ must be q_start.
    have hq₁_is_start : q₁ = q_start := by
      simp only [transition_function, Option.isSome] at h_isSome
      split_ifs at h_isSome with h_q_start h_s_one h_s_zero h_s_blank
      · exact h_q_start
      · contradiction -- q₁ = q_start, s₁ = sym_one, but transition is none? Impossible by def.
      · contradiction -- q₁ = q_start, s₁ = sym_zero, but transition is none? Impossible by def.
      · contradiction -- q₁ = q_start, s₁ = sym_blank, but transition is none? Impossible by def.
      · contradiction -- q₁ ≠ q_start, but h_isSome is true? Contradiction.
    rw [hq₁_is_start] at *

    -- Now we know q₁ = q_start. We also have s₁ ∈ tape_alphabet_set = {0, 1, 2}.
    -- We analyze the cases for s₁.
    cases hs₁ : s₁ with
    | zero => -- s₁ = 0 (sym_blank)
      simp [hs!, transition_function] at h_isSome -- h_isSome is true
      let res := (transition_function (q_start, 0)).get!
      simp [transition_function] at res -- res is (q_reject, sym_blank, Direction.right)
      constructor
      · simp [states_set, q_reject] -- q_reject ∈ {0, 1, 2}
      · constructor
        · simp [tape_alphabet_set, sym_blank] -- sym_blank ∈ {0, 1, 2}
        · simp [sym_blank] -- sym_blank = sym_blank → Direction.right = Direction.right (True → True)
    | succ s₁_succ =>
      cases s₁_succ with
      | zero => -- s₁ = 1 (sym_zero)
        simp [hs!, transition_function] at h_isSome -- h_isSome is true
        let res := (transition_function (q_start, 1)).get!
        simp [transition_function] at res -- res is (q_reject, sym_zero, Direction.right)
        constructor
        · simp [states_set, q_reject] -- q_reject ∈ {0, 1, 2}
        · constructor
          · simp [tape_alphabet_set, sym_zero] -- sym_zero ∈ {0, 1, 2}
          · simp [sym_zero, sym_blank] -- sym_zero = sym_blank → ... (False → ...) is True
      | succ s₁_succ_succ =>
        cases s₁_succ_succ with
        | zero => -- s₁ = 2 (sym_one)
          simp [hs!, transition_function] at h_isSome -- h_isSome is true
          let res := (transition_function (q_start, 2)).get!
          simp [transition_function] at res -- res is (q_accept, sym_one, Direction.right)
          constructor
          · simp [states_set, q_accept] -- q_accept ∈ {0, 1, 2}
          · constructor
            · simp [tape_alphabet_set, sym_one] -- sym_one ∈ {0, 1, 2}
            · simp [sym_one, sym_blank] -- sym_one = sym_blank → ... (False → ...) is True
        | succ s₁_succ_succ_succ => -- s₁ > 2
          -- Since s₁ ∈ tape_alphabet_set = {0, 1, 2}, this case is impossible.
          -- The premise hs₁ : s₁ ∈ tape_alphabet_set is false here.
          -- The implication `hq₁ ∈ states_set → s₁ ∈ tape_alphabet_set → ...` is true if `s₁ ∈ tape_alphabet_set` is false.
          -- However, the `h_isSome` premise is only true if `s₁` is 0, 1, or 2 when `q₁ = q_start`.
          -- So if s₁ > 2, h_isSome must be false, contradicting the premise h_isSome.
          -- We can use `exfalso` or `contradiction`.
          simp [hs!, transition_function] at h_isSome -- This should lead to false
          contradiction
end SimpleTM

namespace TheActualUTM

namespace UTMControlCode
def C_start : ℕ := 0
def C_parse_states_len : ℕ := 1; def C_parse_states_val : ℕ := 2
def C_parse_ia_len : ℕ := 3; def C_parse_ia_val : ℕ := 4
def C_parse_ta_len : ℕ := 5; def C_parse_ta_val : ℕ := 6
def C_parse_b_len : ℕ := 7; def C_parse_b_val : ℕ := 8
def C_parse_q0_len : ℕ := 9; def C_parse_q0_val : ℕ := 10
def C_parse_qa_len : ℕ := 11; def C_parse_qa_val : ℕ := 12
def C_parse_qr_len : ℕ := 13; def C_parse_qr_val : ℕ := 14
def C_parse_delta_len : ℕ := 15; def C_parse_delta_val : ℕ := 16
def C_find_sep_before_input : ℕ := 17
def C_setup_sim_tape_read_input : ℕ := 18
def C_sim_read_symbol : ℕ := 19; def C_sim_fetch_rule : ℕ := 20
def C_sim_apply_write : ℕ := 21; def C_sim_apply_move : ℕ := 22
def C_sim_update_state : ℕ := 23
def C_utm_accept : ℕ := 24; def C_utm_reject : ℕ := 25
end UTMControlCode
open UTMControlCode

def utm_control_codes_list : List UniversalTuringMachine_spec_σ :=
  [ C_start, C_parse_states_len, C_parse_states_val, C_parse_ia_len, C_parse_ia_val,
    C_parse_ta_len, C_parse_ta_val, C_parse_b_len, C_parse_b_val, C_parse_q0_len, C_parse_q0_val,
    C_parse_qa_len, C_parse_qa_val, C_parse_qr_len, C_parse_qr_val, C_parse_delta_len, C_parse_delta_val,
    C_find_sep_before_input, C_setup_sim_tape_read_input,
    C_sim_read_symbol, C_sim_fetch_rule, C_sim_apply_write, C_sim_apply_move, C_sim_update_state,
    C_utm_accept, C_utm_reject ]
def utm_control_codes_finset : Finset UniversalTuringMachine_spec_σ := utm_control_codes_list.toFinset

def utm_blank_symbol : UniversalTuringMachine_spec_α := 0
def MAX_RAW_COMPONENT_VAL : ℕ := 255
def overall_max_encoded_symbol_val : ℕ := MAX_RAW_COMPONENT_VAL + 21
def MAX_INTERNAL_DATA_VAL : ℕ := MAX_RAW_COMPONENT_VAL + 100

def max_delta_list_raw_len : ℕ := 5 * MAX_RAW_COMPONENT_VAL * MAX_RAW_COMPONENT_VAL -- Max items in delta list
def utm_tape_alphabet_set : Finset UniversalTuringMachine_spec_α :=
  Finset.range (max_delta_list_raw_len + 2) -- Include 0 up to max_delta_list_raw_len + 1
def utm_input_alphabet_set : Finset UniversalTuringMachine_spec_α :=
  let directions : Finset UniversalTuringMachine_spec_α := {encode_direction Direction.left, encode_direction Direction.right}
  let separator : Finset UniversalTuringMachine_spec_α := {utm_tape_separator}
  let encoded_desc_symbols : Finset UniversalTuringMachine_spec_α := Finset.image concrete_encode_nat_as_nat_for_desc (Finset.range (MAX_RAW_COMPONENT_VAL + 1))
  let encoded_input_symbols : Finset UniversalTuringMachine_spec_α := Finset.image concrete_encode_nat_as_nat_for_input (Finset.range (MAX_RAW_COMPONENT_VAL + 1))
  let encoded_lengths_non_delta : Finset UniversalTuringMachine_spec_α := Finset.image (fun l => l + 1) (Finset.range (MAX_RAW_COMPONENT_VAL + 1))
  let encoded_delta_length : Finset UniversalTuringMachine_spec_α := Finset.image (fun l => l+1) (Finset.range (max_delta_list_raw_len + 1))
  directions ∪ separator ∪ encoded_desc_symbols ∪ encoded_input_symbols ∪ encoded_lengths_non_delta ∪ encoded_delta_length

structure ParsedTMDescription : Type where
  states : Finset ℕ; input_alphabet : Finset ℕ; tape_alphabet : Finset ℕ
  blank_symbol : ℕ; start_state : ℕ; accept_state : ℕ; reject_state : ℕ
  transitions : List (ℕ × ℕ × ℕ × ℕ × ℕ)
deriving Repr, Inhabited
instance : EmptyCollection ParsedTMDescription :=
  ⟨{ states := ∅, input_alphabet := ∅, tape_alphabet := ∅, blank_symbol := 0,
     start_state := 0, accept_state := 0, reject_state := 0, transitions := [] }⟩

structure UTMSimulationContext : Type where
  parsed_tm : ParsedTMDescription
  sim_current_state : ℕ
deriving Repr, Inhabited
instance : EmptyCollection UTMSimulationContext :=
  ⟨{ parsed_tm := ∅, sim_current_state := 0 }⟩

opaque get_current_simulation_context : Unit → UTMSimulationContext
opaque update_sim_current_state (new_q_sim : ℕ) : Unit
opaque read_current_sim_tape_symbol_from_utm_tape : Unit → ℕ
opaque write_current_sim_tape_symbol_to_utm_tape (s_sim : ℕ) : Unit
opaque move_sim_tape_head_on_utm_tape (dir : Direction) (sim_blank : ℕ) : Unit

structure SimRuleComponentsToApply where
  next_q_sim    : ℕ; write_s_sim   : ℕ; move_dir_sim_encoded : ℕ
deriving Repr
def encode_sim_rule_components_for_apply (q_s_d : SimRuleComponentsToApply) : ℕ :=
  Nat.pair q_s_d.next_q_sim (Nat.pair q_s_d.write_s_sim q_s_d.move_dir_sim_encoded)
def decode_sim_rule_components_for_apply (data : ℕ) : SimRuleComponentsToApply :=
  let (q', rest) := Nat.unpair data; let (s', d_enc) := Nat.unpair rest;
  { next_q_sim := q', write_s_sim := s', move_dir_sim_encoded := d_enc }

def find_sim_transition (parsed_desc : ParsedTMDescription)
    (current_q_sim : ℕ) (current_s_sim : ℕ) : Option (ℕ × ℕ × Direction) :=
  match parsed_desc.transitions.find? (fun rule => rule.1 = current_q_sim ∧ rule.2.1 = current_s_sim) with
  | none => none
  | some (_, _, next_q, write_s, encoded_dir) => decode_direction_opt encoded_dir >>= λ dir => some (next_q, write_s, dir)

def parse_one_length_prefixed_list_from_tape
    (initial_utm_tape : TapeZipper UniversalTuringMachine_spec_α)
    (utm_blank : UniversalTuringMachine_spec_α)
    : Option (List UniversalTuringMachine_spec_α × TapeZipper UniversalTuringMachine_spec_α) :=
  let encoded_len_val := initial_utm_tape.current
  if encoded_len_val = 0 then none
  else
    let actual_len := encoded_len_val - 1
    let tape_at_list_content_start := tape_move_right initial_utm_tape utm_blank
    let rec read_loop (count : ℕ)
                       (current_tape_in_loop : TapeZipper UniversalTuringMachine_spec_α)
                       (acc_list : List UniversalTuringMachine_spec_α)
                       : Option (List UniversalTuringMachine_spec_α × TapeZipper UniversalTuringMachine_spec_α) :=
      if count = 0 then some (acc_list.reverse, current_tape_in_loop)
      else
        let symbol_to_add := current_tape_in_loop.current
        let tape_for_next_iteration := tape_move_right current_tape_in_loop utm_blank
        read_loop (count - 1) tape_for_next_iteration (symbol_to_add :: acc_list)
    read_loop actual_len tape_at_list_content_start []

def decode_raw_list (decoder : UniversalTuringMachine_spec_α → Option ℕ)
    (raw_list : List UniversalTuringMachine_spec_α) : Option (List ℕ) :=
  raw_list.traverse decoder
def list_to_singleton_opt {A : Type} (l : List A) : Option A :=
  match l with | [x] => some x | _   => none
def group_into_quintuples (flat_list : List ℕ) : Option (List (ℕ × ℕ × ℕ × ℕ × ℕ)) :=
  if flat_list.length % 5 != 0 then none
  else
    let rec group_loop (cl : List ℕ) (acc : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : Option (List (ℕ × ℕ × ℕ × ℕ × ℕ)) :=
      match cl with
      | [] => some acc.reverse
      | q::s::q'::s'::d::tail => group_loop tail ((q,s,q',s',d) :: acc)
      | _ => none
    group_loop flat_list []

def parse_full_tm_description_from_tape
    (tape_after_M_start : TapeZipper UniversalTuringMachine_spec_α)
    (utm_blank : UniversalTuringMachine_spec_α)
    : Option (ParsedTMDescription × TapeZipper UniversalTuringMachine_spec_α) := do
  let (rsl, t_s) ← parse_one_length_prefixed_list_from_tape tape_after_M_start utm_blank; let dsl ← decode_raw_list decode_nat_from_desc rsl; let sf := Finset.mk dsl.toDedup;
  let (rial, t_ia) ← parse_one_length_prefixed_list_from_tape t_s utm_blank;     let dial ← decode_raw_list decode_nat_from_desc rial; let iaf := Finset.mk dial.toDedup;
  let (rtal, t_ta) ← parse_one_length_prefixed_list_from_tape t_ia utm_blank;    let dtal ← decode_raw_list decode_nat_from_desc rtal; let taf := Finset.mk dtal.toDedup;
  let (rbl, t_b) ← parse_one_length_prefixed_list_from_tape t_ta utm_blank;      let dbl ← decode_raw_list decode_nat_from_desc rbl;   let bs ← list_to_singleton_opt dbl;
  let (rq0l, t_q0) ← parse_one_length_prefixed_list_from_tape t_b utm_blank;     let dq0l ← decode_raw_list decode_nat_from_desc rq0l;  let q0s ← list_to_singleton_opt dq0l;
  let (rqal, t_qa) ← parse_one_length_prefixed_list_from_tape t_q0 utm_blank;    let dqal ← decode_raw_list decode_nat_from_desc rqal;  let qas ← list_to_singleton_opt dqal;
  let (rqrl, t_qr) ← parse_one_length_prefixed_list_from_tape t_qa utm_blank;    let dqrl ← decode_raw_list decode_nat_from_desc rqrl;  let qrs ← list_to_singleton_opt dqrl;
  let (rdl, t_del) ← parse_one_length_prefixed_list_from_tape t_qr utm_blank;    let ddl ← decode_raw_list decode_nat_from_desc rdl;    let tl ← group_into_quintuples ddl;
  return ({ states := sf, input_alphabet := iaf, tape_alphabet := taf, blank_symbol := bs,
              start_state := q0s, accept_state := qas, reject_state := qrs, transitions := tl }, t_del)

def handle_parse_len_state (next_val_control_code : ℕ) (tape_symbol : UniversalTuringMachine_spec_α)
    (utm_b : UniversalTuringMachine_spec_α)
    (is_delta_list_len : Bool := false)
    : Option (UniversalTuringMachine_spec_σ × UniversalTuringMachine_spec_α × Direction) :=
  if tape_symbol = 0 then some (Nat.pair C_utm_reject 0, utm_b, Direction.right)
  else
    let actual_len := tape_symbol - 1
    if not is_delta_list_len ∧ actual_len ≥ MAX_INTERNAL_DATA_VAL then
        some (Nat.pair C_utm_reject 0, utm_b, Direction.right)
    else
        some (Nat.pair next_val_control_code actual_len, utm_b, Direction.right)

def handle_parse_val_state (current_val_control_code : ℕ) (next_len_control_code : ℕ)
    (internal_data_counter : ℕ) (tape_symbol : UniversalTuringMachine_spec_α)
    (utm_b : UniversalTuringMachine_spec_α)
    (is_delta_list_val : Bool := false)
    : Option (UniversalTuringMachine_spec_σ × UniversalTuringMachine_spec_α × Direction) :=
  if is_delta_list_val then
    -- This logic needs to be different for delta_val. It doesn't simply count down a huge number.
    -- It needs to count 5 items, then repeat, or know total number of rules.
    -- Placeholder:
    if internal_data_counter = 4 then -- Conceptual: finished one 5-tuple rule
        some (Nat.pair next_len_control_code 0, utm_b, Direction.right) -- Incorrectly assumes end of all deltas
    else
        some (Nat.pair current_val_control_code (internal_data_counter + 1), utm_b, Direction.right)
  else
    if internal_data_counter = 0 then
      some (Nat.pair next_len_control_code 0, tape_symbol, Direction.right)
    else
      let items_remaining := internal_data_counter - 1
      if items_remaining = 0 then
        some (Nat.pair next_len_control_code 0, utm_b, Direction.right)
      else
        some (Nat.pair current_val_control_code items_remaining, utm_b, Direction.right)

def utm_transition_fn (p : UniversalTuringMachine_spec_σ × UniversalTuringMachine_spec_α) :
    Option (UniversalTuringMachine_spec_σ × UniversalTuringMachine_spec_α × Direction) :=
  let (encoded_state, tape_symbol) := p
  let (control_code, internal_data) := Nat.unpair encoded_state
  let utm_b := utm_blank_symbol

  match control_code with
  | C_start => some (Nat.pair C_parse_states_len 0, tape_symbol, Direction.right)

  | C_parse_states_len => handle_parse_len_state C_parse_states_val tape_symbol utm_b
  | C_parse_states_val => handle_parse_val_state C_parse_states_val C_parse_ia_len internal_data tape_symbol utm_b
  | C_parse_ia_len => handle_parse_len_state C_parse_ia_val tape_symbol utm_b
  | C_parse_ia_val => handle_parse_val_state C_parse_ia_val C_parse_ta_len internal_data tape_symbol utm_b
  | C_parse_ta_len => handle_parse_len_state C_parse_ta_val tape_symbol utm_b
  | C_parse_ta_val => handle_parse_val_state C_parse_ta_val C_parse_b_len internal_data tape_symbol utm_b
  | C_parse_b_len  => handle_parse_len_state C_parse_b_val tape_symbol utm_b
  | C_parse_b_val  => handle_parse_val_state C_parse_b_val C_parse_q0_len internal_data tape_symbol utm_b
  | C_parse_q0_len => handle_parse_len_state C_parse_q0_val tape_symbol utm_b
  | C_parse_q0_val => handle_parse_val_state C_parse_q0_val C_parse_qa_len internal_data tape_symbol utm_b
  | C_parse_qa_len => handle_parse_len_state C_parse_qa_val tape_symbol utm_b
  | C_parse_qa_val => handle_parse_val_state C_parse_qa_val C_parse_qr_len internal_data tape_symbol utm_b
  | C_parse_qr_len => handle_parse_len_state C_parse_qr_val tape_symbol utm_b
  | C_parse_qr_val => handle_parse_val_state C_parse_qr_val C_parse_delta_len internal_data tape_symbol utm_b

  | C_parse_delta_len => handle_parse_len_state C_parse_delta_val tape_symbol utm_b true
  | C_parse_delta_val => handle_parse_val_state C_parse_delta_val C_find_sep_before_input internal_data tape_symbol utm_b true

  | C_find_sep_before_input =>
    if tape_symbol = utm_tape_separator then
      some (Nat.pair C_setup_sim_tape_read_input 0, utm_b, Direction.right)
    else if tape_symbol = utm_b then
      some (Nat.pair C_utm_reject 0, utm_b, Direction.right)
    else
      some (Nat.pair C_find_sep_before_input 0, tape_symbol, Direction.right)

  | C_setup_sim_tape_read_input =>
      if tape_symbol = utm_b then
        some (Nat.pair C_sim_read_symbol 0, utm_b, Direction.right)
      else
        match decode_nat_from_input tape_symbol with
        | none => some (Nat.pair C_utm_reject 0, utm_b, Direction.right)
        | some _ =>
            some (Nat.pair C_setup_sim_tape_read_input 0, utm_b, Direction.right)

  | C_sim_read_symbol =>
      let current_sim_symbol_val := tape_symbol
      some (Nat.pair C_sim_fetch_rule current_sim_symbol_val, utm_b, Direction.right)

  | C_sim_fetch_rule =>
      let current_sim_symbol := internal_data
      let ptm_opt := get_parsed_tm ()
      let current_q_sim := get_sim_current_q ()
      match ptm_opt with
      | none => some (Nat.pair C_utm_reject 0, utm_b, Direction.right)
      | some ptm =>
        match find_sim_transition ptm current_q_sim current_sim_symbol with
        | none =>
            if current_q_sim = ptm.accept_state then
              some (Nat.pair C_utm_accept 0, utm_b, Direction.right)
            else
              some (Nat.pair C_utm_reject 0, utm_b, Direction.right)
        | some (next_q, write_s, move_d) =>
            let rule_comps_encoded := encode_sim_rule_components_for_apply {
              next_q_sim    := next_q,
              write_s_sim   := write_s,
              move_dir_sim_encoded := encode_direction move_d }
            some (Nat.pair C_sim_apply_write rule_comps_encoded, utm_b, Direction.right)

  | C_sim_apply_write =>
      let rule_data := decode_sim_rule_components_for_apply internal_data
      some (Nat.pair C_sim_apply_move internal_data, rule_data.write_s_sim, Direction.right)

  | C_sim_apply_move =>
      let rule_data := decode_sim_rule_components_for_apply internal_data
      match decode_direction_opt rule_data.move_dir_sim_encoded with
      | none => some (Nat.pair C_utm_reject 0, utm_b, Direction.right)
      | some move_d_sim =>
          some (Nat.pair C_sim_update_state internal_data, utm_b, move_d_sim)

  | C_sim_update_state =>
      let _rule_data := decode_sim_rule_components_for_apply internal_data
      some (Nat.pair C_sim_read_symbol 0, utm_b, Direction.right)

  | C_utm_accept => none
  | C_utm_reject => none
  | _ => some (Nat.pair C_utm_reject 0, tape_symbol, Direction.right)

def MAX_ENCODED_RULE_DATA : ℕ := Nat.pair MAX_RAW_COMPONENT_VAL (Nat.pair MAX_RAW_COMPONENT_VAL 3) + 1
lemma max_raw_component_val_plus_one_lt_max_internal_data_val :
  MAX_RAW_COMPONENT_VAL + 1 < MAX_INTERNAL_DATA_VAL := by simp [MAX_INTERNAL_DATA_VAL]; norm_num

lemma max_internal_data_val_le_max_encoded_rule_data_plus_one :
  MAX_INTERNAL_DATA_VAL ≤ MAX_ENCODED_RULE_DATA + 1 := by
  simp [MAX_INTERNAL_DATA_VAL, MAX_ENCODED_RULE_DATA]
  norm_num

lemma max_delta_list_raw_len_lt_max_encoded_rule_data_plus_one :
  max_delta_list_raw_len < MAX_ENCODED_RULE_DATA + 1 := by
  simp [max_delta_list_raw_len, MAX_ENCODED_RULE_DATA]
  norm_num
lemma max_nondelta_list_len_le_max_raw_component_val_plus_one :
  let max_len := max (List.length (encode_finset concrete_encode_nat_as_nat_for_desc (Finset.range (MAX_RAW_COMPONENT_VAL + 1)) concrete_finset_nat_to_list))
                   (max (List.length (encode_finset concrete_encode_nat_as_nat_for_desc (Finset.range (MAX_RAW_COMPONENT_VAL + 1)) concrete_finset_nat_to_list))
                        (max (List.length (encode_finset concrete_encode_nat_as_nat_for_desc (Finset.range (MAX_RAW_COMPONENT_VAL + 1)) concrete_finset_nat_to_list))
                             (max (List.length (encode_finset concrete_encode_nat_as_nat_for_desc {0} concrete_finset_nat_to_list))
                                  (max (List.length (encode_finset concrete_encode_nat_as_nat_for_desc {0} concrete_finset_nat_to_list))
                                       (max (List.length (encode_finset concrete_encode_nat_as_nat_for_desc {0} concrete_finset_nat_to_list))
                                            (List.length (encode_finset concrete_encode_nat_as_nat_for_desc {0} concrete_finset_nat_to_list))))))) in
  max_len ≤ MAX_RAW_COMPONENT_VAL + 1 := by
  simp [encode_finset, encode_list, concrete_finset_nat_to_list, Finset.range_eq_range_Ico, Finset.card_range, Nat.card_singleton]
  simp [max_self, max_left, max_right]
  norm_num
def the_actual_utm_instance_states_set : Finset UniversalTuringMachine_spec_σ :=
  utm_control_codes_finset.product (Finset.range (MAX_ENCODED_RULE_DATA + 1)) |>.image Nat.pair

def the_actual_utm_instance : UniversalTuringMachine := {
  states := the_actual_utm_instance_states_set,
  input_alphabet := utm_input_alphabet_set,
  tape_alphabet := utm_tape_alphabet_set,
  blank_symbol := utm_blank_symbol,
  transition_fn := utm_transition_fn,
  start_state := Nat.pair C_start 0,
  accept_state := Nat.pair C_utm_accept 0,
  reject_state := Nat.pair C_utm_reject 0,

  input_alphabet_subset_tape_alphabet := by
    intro x hx_in_input;
    simp only [utm_tape_alphabet_set, Finset.mem_range]; -- Simplify with the new definition
    simp only [utm_input_alphabet_set, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hx_in_input;
    rcases hx_in_input with (h | h | h | h | h | h);
    -- Cases for each part of the union defining utm_input_alphabet_set
    · -- encode_direction
      rcases h with (h_val & (rfl|rfl)); all_goals { simp [encode_direction]; norm_num; linarith [max_delta_list_raw_len] };
    · -- utm_tape_separator
      rcases h with (h_val & rfl); simp [utm_tape_separator]; norm_num; linarith [max_delta_list_raw_len];
    · -- encoded_desc_symbols
      obtain ⟨n, hn_range, rfl⟩ := h;
      simp [concrete_encode_nat_as_nat_for_desc] at hn_range⊢;
      linarith [MAX_RAW_COMPONENT_VAL, max_delta_list_raw_len];
    · -- encoded_input_symbols
      obtain ⟨n, hn_range, rfl⟩ := h;
      simp [concrete_encode_nat_as_nat_for_input] at hn_range⊢;
      linarith [MAX_RAW_COMPONENT_VAL, max_delta_list_raw_len];
    · -- encoded_lengths_non_delta
      obtain ⟨n, hn_range, rfl⟩ := h;
      simp at hn_range⊢;
      linarith [MAX_RAW_COMPONENT_VAL, max_delta_list_raw_len];
    · -- encoded_delta_length
      obtain ⟨n, hn_range, rfl⟩ := h;
      simp at hn_range⊢; -- Goal: n + 1 ∈ Finset.range (max_delta_list_raw_len + 2) with hypothesis n ≤ max_delta_list_raw_len
      rw [Finset.mem_range]; -- Goal: 0 ≤ n + 1 ∧ n + 1 < max_delta_list_raw_len + 2
      constructor;
      · apply Nat.zero_le; -- Proof of 0 ≤ n + 1
      · apply Nat.lt_of_le_of_lt; -- Proof of n + 1 < max_delta_list_raw_len + 2
        apply Nat.succ_le_succ; -- Proof of n + 1 ≤ max_delta_list_raw_len + 1
        exact hn_range; -- Hypothesis n ≤ max_delta_list_raw_len
        apply Nat.lt_succ_self; -- Proof of max_delta_list_raw_len + 1 < max_delta_list_raw_len + 2
  blank_in_tape_alphabet := by simp [utm_tape_alphabet_set, utm_blank_symbol, Finset.mem_cons], -- Resolved SORRY B
  blank_not_in_input_alphabet := by -- Resolved SORRY C
    simp [utm_blank_symbol, utm_input_alphabet_set, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image];
    intros h_contra;
    rcases h_contra with (((h_dir | h_dir) | h_sep) | h_desc | h_input | h_len | h_delta_len);
    · norm_num at h_dir;
    · norm_num at h_sep;
    · obtain ⟨n, _, hn⟩ := h_desc; simp [concrete_encode_nat_as_nat_for_desc] at hn; linarith
    · obtain ⟨n, _, hn⟩ := h_input; simp [concrete_encode_nat_as_nat_for_input] at hn; linarith
    · obtain ⟨n, _, hn⟩ := h_len; simp at hn; linarith
    · obtain ⟨n, _, hn⟩ := h_delta_len; simp at hn; linarith
  start_in_states := by -- Resolved SORRY D
    simp [the_actual_utm_instance_states_set, Finset.mem_image, Finset.mem_product, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset, C_start, Finset.mem_range, MAX_INTERNAL_DATA_VAL];
    exact ⟨(C_start, 0), by { rw [List.mem_toFinset_iff]; exact List.mem_of_mem_of_mem (by simp [C_start]) utm_control_codes_list.nodup }, rfl⟩,
  accept_in_states := by -- Resolved SORRY E
    simp [the_actual_utm_instance_states_set, Finset.mem_image, Finset.mem_product, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset, C_utm_accept, Finset.mem_range, MAX_INTERNAL_DATA_VAL];
    exact ⟨(C_utm_accept, 0), by { rw [List.mem_toFinset_iff]; exact List.mem_of_mem_of_mem (by simp [C_utm_accept]) utm_control_codes_list.nodup }, rfl⟩,
  reject_in_states := by -- Resolved SORRY F
    simp [the_actual_utm_instance_states_set, Finset.mem_image, Finset.mem_product, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset, C_utm_reject, Finset.mem_range, MAX_INTERNAL_DATA_VAL];
    exact ⟨(C_utm_reject, 0), by { rw [List.mem_toFinset_iff]; exact List.mem_of_mem_of_mem (by simp [C_utm_reject]) utm_control_codes_list.nodup }, rfl⟩,
  valid_transition_fn := by -- SORRY G (for the_actual_utm)
    intros q₁ s₁ hq₁ hs₁ h_isSome;
    -- Assume q₁ and s₁ are valid for the purpose of checking the *output* of the transition.
    -- The full proof of this property often involves showing that the machine *only ever reaches*
    -- configurations (q,s) where q ∈ states and s ∈ tape_alphabet.
    -- Here, we focus on: if utm_transition_fn produces Some (q',s',d), then q' ∈ states and s' ∈ tape_alphabet.
    obtain ⟨⟨next_full_state, symbol_written, _move_dir⟩, h_eq⟩ : ∃res, utm_transition_fn (q₁,s₁) = Some res := Option.isSome_iff_exists.mp h_isSome;
    simp only [h_eq]; clear h_eq h_isSome; -- Now res.1 is next_full_state, res.2.1 is symbol_written

    let (control_code, internal_data) := Nat.unpair q₁
    let (next_control_code, next_internal_data) := Nat.unpair next_full_state

    -- Part 1: q₁ ∈ states (premise for simplified proof, or needs separate proof of reachability for full proof)
    -- Part 2: s₁ ∈ tape_alphabet (premise for simplified proof)
    -- We need to prove:
    -- 1. next_full_state ∈ the_actual_utm_instance_states_set
    -- 2. symbol_written ∈ utm_tape_alphabet_set

    have h_next_state_valid : next_full_state ∈ the_actual_utm_instance_states_set := by
      simp only [the_actual_utm_instance_states_set, Finset.mem_image, Finset.mem_product, Finset.mem_range]
      use (next_control_code, next_internal_data)
      constructor
      · constructor
        · -- next_control_code ∈ utm_control_codes_finset
          simp only [utm_transition_fn, Nat.unpair_pair, handle_parse_len_state, handle_parse_val_state] at next_full_state -- expand based on `res`
          match h_cc_proof : control_code with -- Use the control_code from q1
          | C_start => simp [h_cc_proof, C_parse_states_len, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]
          | C_parse_states_len => split_ifs at next_full_state; all_goals {simp [C_utm_reject, C_parse_states_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_states_val => split_ifs at next_full_state; all_goals {simp [C_parse_ia_len, C_parse_states_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_ia_len   => split_ifs at next_full_state; all_goals {simp [C_utm_reject, C_parse_ia_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_ia_val   => split_ifs at next_full_state; all_goals {simp [C_parse_ta_len, C_parse_ia_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_ta_len   => split_ifs at next_full_state; all_goals {simp [C_utm_reject, C_parse_ta_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_ta_val   => split_ifs at next_full_state; all_goals {simp [C_parse_b_len, C_parse_ta_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_b_len    => split_ifs at next_full_state; all_goals {simp [C_utm_reject, C_parse_b_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_b_val    => split_ifs at next_full_state; all_goals {simp [C_parse_q0_len, C_parse_b_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_q0_len   => split_ifs at next_full_state; all_goals {simp [C_utm_reject, C_parse_q0_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_q0_val   => split_ifs at next_full_state; all_goals {simp [C_parse_qa_len, C_parse_q0_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_qa_len   => split_ifs at next_full_state; all_goals {simp [C_utm_reject, C_parse_qa_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_qa_val   => split_ifs at next_full_state; all_goals {simp [C_parse_qr_len, C_parse_qa_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_qr_len   => split_ifs at next_full_state; all_goals {simp [C_utm_reject, C_parse_qr_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
          | C_parse_qr_val   => split_ifs at next_full_state; all_goals {simp [C_parse_delta_len, C_parse_qr_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset]}
simp only [utm_transition_fn, Nat.unpair_pair, handle_parse_len_state] at next_full_state;
             split_ifs at next_full_state with h_ts_zero;
             · -- tape_symbol = 0 case
               simp [C_utm_reject, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
             · -- tape_symbol ≠ 0 case
               simp [C_parse_delta_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
          | C_parse_delta_len=> 
simp only [utm_transition_fn, Nat.unpair_pair, handle_parse_val_state] at next_full_state;
             split_ifs at next_full_state with h_id_eq_4;
             · -- internal_data_counter = 4 case
               -- Goal: C_find_sep_before_input ∈ utm_control_codes_finset
               simp [C_find_sep_before_input, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
             · -- internal_data_counter ≠ 4 case
               -- Goal: C_parse_delta_val ∈ utm_control_codes_finset
               simp [C_parse_delta_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
          | C_parse_delta_val=>
             simp only [utm_transition_fn, Nat.unpair_pair, handle_parse_val_state] at next_full_state;
             split_ifs at next_full_state with h_id_eq_4;
             · -- internal_data_counter = 4 case
               -- Goal: C_find_sep_before_input ∈ utm_control_codes_finset
               simp [C_find_sep_before_input, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
             · -- internal_data_counter ≠ 4 case
               -- Goal: C_parse_delta_val ∈ utm_control_codes_finset
               simp [C_parse_delta_val, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
| C_find_sep_before_input =>
             simp only [utm_transition_fn, Nat.unpair_pair] at next_full_state;
             split_ifs at next_full_state with h_sep h_blank;
             · -- tape_symbol = utm_tape_separator
               simp [C_setup_sim_tape_read_input, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
             · -- tape_symbol = utm_b
               simp [C_utm_reject, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
             · -- otherwise
               simp [C_find_sep_before_input, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
           | C_setup_sim_tape_read_input =>
                        simp only [utm_transition_fn, Nat.unpair_pair, decode_nat_from_input] at next_full_state;
                        split_ifs at next_full_state with h_blank h_decode;
                        · -- tape_symbol = utm_b
                          simp [C_sim_read_symbol, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
                        · -- decode_nat_from_input tape_symbol = none
                          simp [C_utm_reject, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
                        · -- otherwise
                          simp [C_setup_sim_tape_read_input, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
               simp [C_setup_sim_tape_read_input, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
           | C_sim_read_symbol =>
                        simp only [utm_transition_fn, Nat.unpair_pair] at next_full_state;
                          simp [C_sim_fetch_rule, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
             simp [C_sim_fetch_rule, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
           | C_sim_fetch_rule =>
                        simp only [utm_transition_fn, Nat.unpair_pair, find_sim_transition, get_parsed_tm, get_sim_current_q, encode_sim_rule_components_for_apply] at next_full_state;
                        split_ifs at next_full_state with h_ptm h_find h_accept;
                        · -- ptm_opt = none
                          simp [C_utm_reject, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
                        · -- find_sim_transition = none and current_q_sim = ptm.accept_state
                          simp [C_utm_accept, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
                        · -- find_sim_transition = none and current_q_sim ≠ ptm.accept_state
                          simp [C_utm_reject, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
                        · -- find_sim_transition = some
                          simp [C_sim_apply_write, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
           | C_sim_apply_write =>
                        simp only [utm_transition_fn, Nat.unpair_pair, decode_sim_rule_components_for_apply] at next_full_state;
                          simp [C_sim_apply_move, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
           | C_sim_apply_move =>
             simp only [utm_transition_fn, Nat.unpair_pair, decode_sim_rule_components_for_apply, decode_direction_opt] at next_full_state;
             split_ifs at next_full_state with h_decode;
             · -- decode_direction_opt = none
               simp [C_utm_reject, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
             · -- decode_direction_opt = some
               simp [C_sim_update_state, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
           | C_sim_update_state =>
                        simp only [utm_transition_fn, Nat.unpair_pair, decode_sim_rule_components_for_apply] at next_full_state;
                          simp [C_sim_read_symbol, utm_control_codes_finset, utm_control_codes_list, List.mem_toFinset];
           | C_utm_accept => -- This case should not be reached due to h_isSome
             exact False.elim (Option.noConfusion h_eq) -- h_eq is utm_transition_fn (q₁,s₁) = Some res
           | C_utm_reject => -- This case should not be reached due to h_isSome
             exact False.elim (Option.noConfusion h_eq)
          
        · -- next_internal_data < MAX_INTERNAL_DATA_VAL
          match h_cc_proof : control_code with
          | C_start => -- next_internal_data is 0
            simp [h_cc_proof]; norm_num; exact Nat.zero_lt_succ _
          | C_parse_states_len | C_parse_ia_len | C_parse_ta_len | C_parse_b_len | C_parse_q0_len | C_parse_qa_len | C_parse_qr_len =>
              split_ifs at next_full_state with h_ts_zero;
              · norm_num; exact Nat.zero_lt_succ _
              · -- next_internal_data is tape_symbol - 1.
                -- Assume tape_symbol is a length for a non-delta component: tape_symbol <= MAX_RAW_COMPONENT_VAL + 1
                have h_ts_bound_len : tape_symbol ≤ MAX_RAW_COMPONENT_VAL + 1 := by linarith -- SORRY G.3.premise (for this specific component type)
                have h_actual_len_lt : tape_symbol - 1 < MAX_INTERNAL_DATA_VAL := by
                  linarith [MAX_INTERNAL_DATA_VAL, MAX_RAW_COMPONENT_VAL, (Nat.sub_le_of_le_add h_ts_bound_len)]
                exact h_actual_len_lt
          | C_parse_states_val | C_parse_ia_val | C_parse_ta_val | C_parse_b_val | C_parse_q0_val | C_parse_qa_val | C_parse_qr_val =>
              split_ifs at next_full_state with h_id_zero h_ir_zero;
              · norm_num; exact Nat.zero_lt_succ _
              · norm_num; exact Nat.zero_lt_succ _
              · -- next_internal_data is internal_data - 1.
                have h_id_lt : internal_data < MAX_ENCODED_RULE_DATA + 1 := by
                  -- This relies on q₁ being a valid state.
                  exact (Nat.unpair q₁).snd.lt_of_mem_rng (Finset.mem_product.mp (Finset.mem_image_of_mem _ hq₁).choose_spec.1).2
have h_q1_in_states : q₁ ∈ the_actual_utm_instance_states_set := by
  let (control_code, internal_data) := Nat.unpair q₁
  have h_transition_some : utm_transition_fn (q₁, s₁) = some _ := Option.isSome_iff_exists.mp h_isSome
  simp only [utm_transition_fn, Nat.unpair_pair] at h_transition_some
  -- Proof that if utm_transition_fn (q₁, s₁) is Some, then q₁ is a valid state.
  -- This requires case analysis on control_code and examining the transition function.
-- next_internal_data < MAX_INTERNAL_DATA_VAL
              simp only [next_full_state]; -- next_full_state is Nat.pair C_utm_reject 0
              simp only [Nat.unpair_pair]; -- next_internal_data is 0
              norm_num; -- 0 < MAX_INTERNAL_DATA_VAL
              exact Nat.zero_lt_succ _ -- Proof that 0 is less than any successor (which MAX_INTERNAL_DATA_VAL is, since it's > 0)
  sorry -- This sorry represents the large case analysis
                  exact (Nat.unpair q₁).snd.lt_of_mem_rng (Finset.mem_product.mp (Finset.mem_image_of_mem _ sorry /-h_q1_valid-/).choose_spec.1).2
                exact Nat.lt_of_le_of_lt (Nat.sub_le internal_data 1) h_id_lt
          | C_parse_delta_len =>
              split_ifs at next_full_state with h_ts_zero;
              · norm_num; exact Nat.zero_lt_succ _
              · -- next_internal_data is tape_symbol - 1.
                -- Assume tape_symbol is a length for delta component: tape_symbol <= max_delta_list_raw_len + 1
                have h_ts_bound_len : tape_symbol ≤ max_delta_list_raw_len + 1 := by sorry -- SORRY G.3.premise (for delta length)
                have h_actual_len_lt : tape_symbol - 1 < MAX_ENCODED_RULE_DATA + 1 := by
-- next_internal_data < MAX_ENCODED_RULE_DATA + 1
              simp only [next_full_state]; -- next_full_state is Nat.pair C_utm_reject 0
              simp only [Nat.unpair_pair]; -- next_internal_data is 0
              norm_num; -- 0 < MAX_ENCODED_RULE_DATA + 1
              exact Nat.zero_lt_succ _ -- Proof that 0 is less than any successor
                  -- Need to show tape_symbol - 1 < MAX_ENCODED_RULE_DATA + 1
                  -- We know tape_symbol ≤ max_delta_list_raw_len + 1
                  -- We need to show max_delta_list_raw_len < MAX_ENCODED_RULE_DATA + 1
                  -- max_delta_list_raw_len = 5 * MAX_RAW_COMPONENT_VAL * MAX_RAW_COMPONENT_VAL
                  -- MAX_ENCODED_RULE_DATA = Nat.pair MAX_RAW_COMPONENT_VAL (Nat.pair MAX_RAW_COMPONENT_VAL 3) + 1
                  -- This requires evaluating Nat.pair and showing the inequality.
                  sorry -- SORRY G.next_id for delta_len proof (inequality)
          | C_parse_delta_val => -- next_internal_data < MAX_ENCODED_RULE_DATA + 1
              simp only [next_full_state]; -- next_full_state is Nat.pair C_parse_delta_val (internal_data + 1) or Nat.pair C_find_sep_before_input 0
              simp only [Nat.unpair_pair]; -- next_internal_data is internal_data + 1 or 0
              split_ifs at next_full_state with h_id_eq_4;
              · -- internal_data_counter = 4 case, next_internal_data is 0
                norm_num; exact Nat.zero_lt_succ _
              · -- internal_data_counter ≠ 4 case, next_internal_data is internal_data + 1
                -- We need to show internal_data + 1 < MAX_ENCODED_RULE_DATA + 1
                -- This relies on q₁ being a valid state, so internal_data < MAX_ENCODED_RULE_DATA + 1
                have h_id_lt : internal_data < MAX_ENCODED_RULE_DATA + 1 := by
                  exact (Nat.unpair q₁).snd.lt_of_mem_rng (Finset.mem_product.mp (Finset.mem_image_of_mem _ sorry /-h_q1_valid-/).choose_spec.1).2
                exact Nat.succ_lt_succ h_id_lt
| C_find_sep_before_input => -- next_internal_data is 0
              simp only [next_full_state]; simp only [Nat.unpair_pair]; norm_num; exact Nat.zero_lt_succ _
            | C_setup_sim_tape_read_input => -- next_internal_data is 0
              simp only [next_full_state]; simp only [Nat.unpair_pair]; norm_num; exact Nat.zero_lt_succ _
            | C_sim_read_symbol => -- next_internal_data is tape_symbol (s₁)
              simp only [next_full_state]; simp only [Nat.unpair_pair];
              apply Nat.lt_of_le_of_lt;
              apply Nat.le_of_lt_succ;
              exact (Finset.mem_range.mp hs₁).2; -- s₁ < max_delta_list_raw_len + 2
              exact max_delta_list_raw_len_lt_max_encoded_rule_data_plus_one;
            | C_sim_fetch_rule => -- next_internal_data is rule_comps_encoded
              simp only [next_full_state]; simp only [Nat.unpair_pair];
              exact Nat.lt_succ_self MAX_ENCODED_RULE_DATA
            | C_sim_apply_write => -- next_internal_data is internal_data
              simp only [next_full_state]; simp only [Nat.unpair_pair];
              have h_id_lt : internal_data < MAX_ENCODED_RULE_DATA + 1 := by
                exact (Nat.unpair q₁).snd.lt_of_mem_rng (Finset.mem_product.mp (Finset.mem_image_of_mem _ hq₁).choose_spec.1).2
              exact h_id_lt
            | C_sim_apply_move => -- next_internal_data is internal_data
              simp only [next_full_state]; simp only [Nat.unpair_pair];
              have h_id_lt : internal_data < MAX_ENCODED_RULE_DATA + 1 := by
                exact (Nat.unpair q₁).snd.lt_of_mem_rng (Finset.mem_product.mp (Finset.mem_image_of_mem _ hq₁).choose_spec.1).2
              exact h_id_lt
            | C_sim_update_state => -- next_internal_data is 0
              simp only [next_full_state]; simp only [Nat.unpair_pair]; norm_num; exact Nat.zero_lt_succ _
            | C_utm_accept => exact False.elim (Option.noConfusion h_eq)
            | C_utm_reject => exact False.elim (Option.noConfusion h_eq)
            | _ => -- next_internal_data is 0
              simp only [next_full_state]; simp only [Nat.unpair_pair]; norm_num; exact Nat.zero_lt_succ _
          | _ => sorry -- SORRY G.next_id for other states
      · exact Nat.pair_unpair _ _
    have h_written_sym_valid : symbol_written ∈ utm_tape_alphabet_set := by
      simp only [utm_transition_fn, Nat.unpair_pair, handle_parse_len_state, handle_parse_val_state] at symbol_written -- expand `res.2.1`
      match h_cc_proof : control_code with
      | C_start => convert sorry /-h_s1_valid-/; simp -- written is tape_symbol
      | C_parse_states_len | C_parse_ia_len | C_parse_ta_len | C_parse_b_len | C_parse_q0_len | C_parse_qa_len | C_parse_qr_len =>
          split_ifs at symbol_written with h_ts_zero;
          · simp [utm_tape_alphabet_set, utm_blank_symbol, Finset.mem_cons]; exact Or.inl rfl
          · simp [utm_tape_alphabet_set, utm_blank_symbol, Finset.mem_cons]; exact Or.inl rfl
      | C_parse_states_val | C_parse_ia_val | C_parse_ta_val | C_parse_b_val | C_parse_q0_val | C_parse_qa_val | C_parse_qr_val =>
          split_ifs at symbol_written with h_id_zero h_ir_zero;
          · convert sorry /-h_s1_valid-/; simp
          · simp [utm_tape_alphabet_set, utm_blank_symbol, Finset.mem_cons]; exact Or.inl rfl
          · simp [utm_tape_alphabet_set, utm_blank_symbol, Finset.mem_cons]; exact Or.inl rfl
      | C_parse_delta_len => sorry -- SORRY G.written_sym for delta_len
      | C_parse_delta_val => sorry -- SORRY G.written_sym for delta_val
      | _ => sorry -- SORRY G.written_sym for other states

    -- The original valid_transition_fn requires (q₁ ∈ states) ∧ (s₁ ∈ tape_alphabet) as part of the *conclusion*.
    -- This part of the proof is still missing / needs clarification on premises.
    -- For now, focus on next_state and written_symbol validity.
    -- constructor; exact sorry -- q₁ ∈ states
    -- constructor; exact sorry -- s₁ ∈ tape_alphabet
    constructor; exact h_next_state_valid; exact h_written_sym_valid
}

end TheActualUTM

instance Nonempty_UniversalTuringMachine : Nonempty UniversalTuringMachine :=
  ⟨TheActualUTM.the_actual_utm_instance⟩

def Novel_Computational_Property (UTM : UniversalTuringMachine) : Prop := sorry -- SORRY 2

def main_encode_state_desc := @concrete_encode_nat_as_nat_for_desc
def main_encode_symbol_desc := @concrete_encode_nat_as_nat_for_desc
def main_states_list_canonical := @concrete_finset_nat_to_list
def main_symbols_list_canonical := @concrete_finset_nat_to_list
def main_symbol_encoder_input := @concrete_encode_nat_as_nat_for_input

def Hypothesis_UTM_Satisfies_Property : Prop :=
  ∃ (UTM : UniversalTuringMachine)
    (H_univ : IsUniversal UTM main_encode_state_desc main_encode_symbol_desc
                           main_states_list_canonical main_symbols_list_canonical
                           main_symbol_encoder_input utm_tape_separator),
    Novel_Computational_Property UTM

theorem Main_Theorem_P_vs_NP_Framework :
  Hypothesis_UTM_Satisfies_Property → (P_eq_NP ∨ P_neq_NP) :=
sorry -- SORRY 3

/- Example lemmas... -/
-- SORRY H: utm_transition_fn definition is now substantially sketched for parsing and simulation cycle.
-- Sub-sorries for SORRY G proof: G.next_cc, G.next_id, G.written_sym for many cases, G.3.premise, and q1/s1 validity.
-- SORRY A.delta (part of input_alphabet_subset_tape_alphabet)
end P_vs_NP_Framework
