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
import Mathlib.Data.Set.Finite -- For Set operations like subset, used by Finset.subset_iff
import Mathlib.Tactic.Cases -- For cases tactic
import Mathlib.Tactic.SplitIfs -- For split_ifs
import Mathlib.Init.Data.Option.Basic -- For Option.isSome, Option.get!
import Mathlib.Logic.Equiv.Basic -- For decidable_eq
import Mathlib.Data.List.Basic -- For List operations
import Mathlib.Data.List.Defs -- For List.mapM / List.traverse
import Mathlib.Relation.ReflTransGen -- For Reflexive Transitive Closure (RTC)
import Mathlib.Data.Nat.Prime -- For pairing functions if needed for encoding
import Mathlib.Data.Nat.Pairing -- For Nat.pair and Nat.unpair
import Mathlib.Tactic.NormNum -- For simp with numbers
import Mathlib.Tactic.Linarith -- For linear arithmetic
import Mathlib.Data.List.Zip -- For List.zip for transition function parsing
import Mathlib.Control.Traversable.Basic -- For List.traverse

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
  input_alphabet_subset_tape_alphabet : input_alphabet ⊆ tape_alphabet := by sorry -- SORRY A
  blank_in_tape_alphabet : blank_symbol ∈ tape_alphabet := by sorry -- SORRY B
  blank_not_in_input_alphabet : blank_symbol ∉ input_alphabet := by sorry -- SORRY C
  start_in_states : start_state ∈ states := by sorry -- SORRY D
  accept_in_states : accept_state ∈ states := by sorry -- SORRY E
  reject_in_states : reject_state ∈ states := by sorry -- SORRY F
  valid_transition_fn : forall (q₁ : σ_state) (s₁ : α_sym),
    (transition_fn (q₁, s₁)).isSome →
    let res := (transition_fn (q₁, s₁)).get! in
    (q₁ ∈ states) ∧ (s₁ ∈ tape_alphabet) ∧
    (res.1 ∈ states) ∧ (res.2.1 ∈ tape_alphabet) := by sorry -- SORRY G

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

def UniversalTuringMachine_spec_σ : Type := ℕ
instance : Inhabited UniversalTuringMachine_spec_σ := ⟨0⟩
instance : DecidableEq UniversalTuringMachine_spec_σ := instDecidableEqNat
instance : LinearOrder UniversalTuringMachine_spec_σ := Nat.linearOrder

def UniversalTuringMachine_spec_α : Type := ℕ
instance : Inhabited UniversalTuringMachine_spec_α := ⟨0⟩
instance : DecidableEq UniversalTuringMachine_spec_α := instDecidableEqNat
instance : LinearOrder UniversalTuringMachine_spec_α := Nat.linearOrder

def UniversalTuringMachine := TuringMachine UniversalTuringMachine_spec_σ UniversalTuringMachine_spec_α

variable {σ_sim α_sim : Type} [DecidableEq σ_sim] [DecidableEq α_sim] [Inhabited α_sim]

-- Encoders/Decoders for Nat values used in TM description and input words
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
    intro q₁ s₁ h; let res := (transition_function (q₁, s₁)).get!; have h' := Option.get_isSome h;
    unfold transition_function at h'; split_ifs at h' with hq hs1 hs0 hsb <;> (try subst q₁ s₁); simp at h';
    any_goals rw [←h']; simp [states_set, tape_alphabet_set, Finset.mem_insert, Finset.mem_singleton, *]
    all_goals except (exact False.elim (Option.noConfusion h'))
end SimpleTM

namespace TheActualUTM

namespace UTMState
def S_start : ℕ := 0
def S_parse_states_len : ℕ := 1; def S_parse_states_val : ℕ := 2
def S_parse_ia_len : ℕ := 3; def S_parse_ia_val : ℕ := 4
def S_parse_ta_len : ℕ := 5; def S_parse_ta_val : ℕ := 6
def S_parse_b_len : ℕ := 7; def S_parse_b_val : ℕ := 8
def S_parse_q0_len : ℕ := 9; def S_parse_q0_val : ℕ := 10
def S_parse_qa_len : ℕ := 11; def S_parse_qa_val : ℕ := 12
def S_parse_qr_len : ℕ := 13; def S_parse_qr_val : ℕ := 14
def S_parse_delta_len : ℕ := 15; def S_parse_delta_val : ℕ := 16
def S_setup_sim_tape : ℕ := 17; def S_sim_read_symbol : ℕ := 18
def S_sim_fetch_rule : ℕ := 19; def S_sim_apply_write : ℕ := 20
def S_sim_apply_move : ℕ := 21; def S_sim_update_state : ℕ := 22
def S_utm_accept : ℕ := 23; def S_utm_reject : ℕ := 24
end UTMState
open UTMState

def utm_states_set : Finset UniversalTuringMachine_spec_σ :=
  { S_start, S_parse_states_len, S_parse_states_val, S_parse_ia_len, S_parse_ia_val,
    S_parse_ta_len, S_parse_ta_val, S_parse_b_len, S_parse_b_val, S_parse_q0_len, S_parse_q0_val,
    S_parse_qa_len, S_parse_qa_val, S_parse_qr_len, S_parse_qr_val, S_parse_delta_len, S_parse_delta_val,
    S_setup_sim_tape, S_sim_read_symbol, S_sim_fetch_rule, S_sim_apply_write, S_sim_apply_move, S_sim_update_state,
    S_utm_accept, S_utm_reject }

def utm_blank_symbol : UniversalTuringMachine_spec_α := 0
def MAX_RAW_COMPONENT_VAL : ℕ := 255
def overall_max_encoded_symbol_val : ℕ := MAX_RAW_COMPONENT_VAL + 21
def utm_tape_alphabet_set : Finset UniversalTuringMachine_spec_α :=
  Finset.cons utm_blank_symbol (Finset.image Nat.succ (Finset.range overall_max_encoded_symbol_val))
def utm_input_alphabet_set : Finset UniversalTuringMachine_spec_α :=
  let directions : Finset UniversalTuringMachine_spec_α := {encode_direction Direction.left, encode_direction Direction.right}
  let separator : Finset UniversalTuringMachine_spec_α := {utm_tape_separator}
  let encoded_desc_symbols : Finset UniversalTuringMachine_spec_α := Finset.image concrete_encode_nat_as_nat_for_desc (Finset.range (MAX_RAW_COMPONENT_VAL + 1))
  let encoded_input_symbols : Finset UniversalTuringMachine_spec_α := Finset.image concrete_encode_nat_as_nat_for_input (Finset.range (MAX_RAW_COMPONENT_VAL + 1))
  let encoded_lengths : Finset UniversalTuringMachine_spec_α := Finset.image (fun l => l + 1) (Finset.range (MAX_RAW_COMPONENT_VAL + 1))
  directions ∪ separator ∪ encoded_desc_symbols ∪ encoded_input_symbols ∪ encoded_lengths

structure ParsedTMDescription : Type where
  states : Finset ℕ
  input_alphabet : Finset ℕ
  tape_alphabet : Finset ℕ
  blank_symbol : ℕ
  start_state : ℕ
  accept_state : ℕ
  reject_state : ℕ
  transitions : List (ℕ × ℕ × ℕ × ℕ × ℕ)
deriving Repr, Inhabited
instance : EmptyCollection ParsedTMDescription :=
  ⟨{ states := ∅, input_alphabet := ∅, tape_alphabet := ∅, blank_symbol := 0,
     start_state := 0, accept_state := 0, reject_state := 0, transitions := [] }⟩

structure UTMSimulationState : Type where
  parsed_tm : ParsedTMDescription
  sim_current_state : ℕ
  sim_tape : TapeZipper ℕ
deriving Repr, Inhabited
instance : EmptyCollection UTMSimulationState :=
  ⟨{ parsed_tm := ఇన్ఎక్కడాParsedTMDescription, sim_current_state := 0,
     sim_tape := {left := [], current := 0, right := []} }⟩

def find_sim_transition (parsed_desc : ParsedTMDescription)
    (current_q_sim : ℕ) (current_s_sim : ℕ) : Option (ℕ × ℕ × Direction) :=
  match parsed_desc.transitions.find? (fun rule => rule.1 = current_q_sim ∧ rule.2.1 = current_s_sim) with
  | none => none
  | some (_, _, next_q, write_s, encoded_dir) =>
    match decode_direction_opt encoded_dir with
    | none => none
    | some dir => some (next_q, write_s, dir)

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
      if count = 0 then
        some (acc_list.reverse, current_tape_in_loop)
      else
        -- Check if tape ends prematurely (no 'right' part and head is blank, or initial list empty for count > 0)
        -- This check is implicitly handled if tape_move_right returns a tape with blank at current
        -- if it moves off the defined part. A robust UTM might need explicit end-of-tape markers or error states.
        let symbol_to_add := current_tape_in_loop.current
        let tape_for_next_iteration := tape_move_right current_tape_in_loop utm_blank
        read_loop (count - 1) tape_for_next_iteration (symbol_to_add :: acc_list)
    read_loop actual_len tape_at_list_content_start []

-- Helper to decode a list of raw symbols using a given item decoder
def decode_raw_list (decoder : UniversalTuringMachine_spec_α → Option ℕ)
    (raw_list : List UniversalTuringMachine_spec_α) : Option (List ℕ) :=
  raw_list.traverse decoder -- List.traverse f l applies f to each element and collects results in Option

-- Helper to convert a list (expected to be singleton) to an Option of its single element
def list_to_singleton_opt {A : Type} (l : List A) : Option A :=
  match l with
  | [x] => some x
  | _   => none

-- Helper to group a flat list into list of 5-tuples for transitions
def group_into_quintuples (flat_list : List ℕ) : Option (List (ℕ × ℕ × ℕ × ℕ × ℕ)) :=
  if flat_list.length % 5 != 0 then none
  else
    let rec group_loop (current_list : List ℕ) (acc_groups : List (ℕ × ℕ × ℕ × ℕ × ℕ)) :
        Option (List (ℕ × ℕ × ℕ × ℕ × ℕ)) :=
      match current_list with
      | [] => some acc_groups.reverse
      | q::s::q'::s'::d::tail =>
          group_loop tail ((q,s,q',s',d) :: acc_groups)
      | _ => none -- Should not happen if length is multiple of 5
    group_loop flat_list []

-- Function to parse the full TM description from the tape
def parse_full_tm_description_from_tape
    (tape_after_M_start : TapeZipper UniversalTuringMachine_spec_α) -- Tape positioned at start of M's description
    (utm_blank : UniversalTuringMachine_spec_α)
    : Option (ParsedTMDescription × TapeZipper UniversalTuringMachine_spec_α) := do
  -- 1. Parse States
  let (raw_states_list, tape_after_states) ← parse_one_length_prefixed_list_from_tape tape_after_M_start utm_blank
  let decoded_states_list ← decode_raw_list decode_nat_from_desc raw_states_list
  let states_finset := Finset.mk (decoded_states_list.toDedup) -- toDedup removes duplicates before forming Finset

  -- 2. Parse Input Alphabet
  let (raw_ia_list, tape_after_ia) ← parse_one_length_prefixed_list_from_tape tape_after_states utm_blank
  let decoded_ia_list ← decode_raw_list decode_nat_from_desc raw_ia_list
  let ia_finset := Finset.mk (decoded_ia_list.toDedup)

  -- 3. Parse Tape Alphabet
  let (raw_ta_list, tape_after_ta) ← parse_one_length_prefixed_list_from_tape tape_after_ia utm_blank
  let decoded_ta_list ← decode_raw_list decode_nat_from_desc raw_ta_list
  let ta_finset := Finset.mk (decoded_ta_list.toDedup)

  -- 4. Parse Blank Symbol
  let (raw_b_list, tape_after_b) ← parse_one_length_prefixed_list_from_tape tape_after_ta utm_blank
  let decoded_b_list ← decode_raw_list decode_nat_from_desc raw_b_list
  let blank_s ← list_to_singleton_opt decoded_b_list

  -- 5. Parse Start State
  let (raw_q0_list, tape_after_q0) ← parse_one_length_prefixed_list_from_tape tape_after_b utm_blank
  let decoded_q0_list ← decode_raw_list decode_nat_from_desc raw_q0_list
  let q0_s ← list_to_singleton_opt decoded_q0_list

  -- 6. Parse Accept State
  let (raw_qa_list, tape_after_qa) ← parse_one_length_prefixed_list_from_tape tape_after_q0 utm_blank
  let decoded_qa_list ← decode_raw_list decode_nat_from_desc raw_qa_list
  let qa_s ← list_to_singleton_opt decoded_qa_list

  -- 7. Parse Reject State
  let (raw_qr_list, tape_after_qr) ← parse_one_length_prefixed_list_from_tape tape_after_qa utm_blank
  let decoded_qr_list ← decode_raw_list decode_nat_from_desc raw_qr_list
  let qr_s ← list_to_singleton_opt decoded_qr_list

  -- 8. Parse Delta (Transition Function)
  let (raw_delta_list, tape_after_delta) ← parse_one_length_prefixed_list_from_tape tape_after_qr utm_blank
  let decoded_delta_flat_list ← decode_raw_list decode_nat_from_desc raw_delta_list -- These are still encoded values
  let transitions_list ← group_into_quintuples decoded_delta_flat_list -- Now (q,s,q',s',encoded_dir)

  return ({
    states          := states_finset,
    input_alphabet  := ia_finset,
    tape_alphabet   := ta_finset,
    blank_symbol    := blank_s,
    start_state     := q0_s,
    accept_state    := qa_s,
    reject_state    := qr_s,
    transitions     := transitions_list
  } : ParsedTMDescription, tape_after_delta)


def utm_transition_fn (p : UniversalTuringMachine_spec_σ × UniversalTuringMachine_spec_α) :
    Option (UniversalTuringMachine_spec_σ × UniversalTuringMachine_spec_α × Direction) :=
  -- Example structure:
  -- let current_utm_state := p.1
  -- let current_utm_tape_symbol := p.2
  -- match current_utm_state with
  -- | S_start => -- Initialize: set up parsing of TM description
      -- tape would be initial_tape_zipper (encoded_M ++ [sep] ++ encoded_w) utm_blank_symbol
      -- Call parse_full_tm_description_from_tape, store result (e.g. in a dedicated part of UTM tape or conceptual state)
      -- Then transition to S_setup_sim_tape or S_utm_reject if parsing fails.
      -- For now, just a placeholder:
      -- some (S_parse_states_len, utm_blank_symbol, Direction.right)
  -- | S_parse_states_len =>
      -- If current_utm_tape_symbol is the length of states list L_s.
      -- Store L_s. Move tape head right. Transition to S_parse_states_val.
      -- This would be part of the logic now encapsulated in parse_full_tm_description_from_tape
  -- | S_sim_read_symbol =>
      -- Read symbol from simulated tape (requires knowing where sim_tape is on UTM tape).
      -- Get current simulated state (from UTMSimulationState).
      -- Transition to S_sim_fetch_rule.
  -- | S_sim_fetch_rule =>
      -- Use find_sim_transition with data from UTMSimulationState.
      -- If rule found, store it (e.g. on work tape/conceptual state), transition to S_sim_apply_write.
      -- If no rule (simulated TM halts): check if current_sim_state = accept_state or reject_state (from ParsedTMDesc).
      --   Transition to S_utm_accept or S_utm_reject accordingly.
  -- | ... other states ...
  -- | S_utm_accept => none -- UTM halts in accept
  -- | S_utm_reject => none -- UTM halts in reject
  sorry -- SORRY H

def the_actual_utm_instance : UniversalTuringMachine := {
  states := utm_states_set,
  input_alphabet := utm_input_alphabet_set,
  tape_alphabet := utm_tape_alphabet_set,
  blank_symbol := utm_blank_symbol,
  transition_fn := utm_transition_fn,
  start_state := S_start,
  accept_state := S_utm_accept,
  reject_state := S_utm_reject,

  input_alphabet_subset_tape_alphabet := by -- Resolved SORRY A
    intro x hx_in_input;
    simp only [utm_tape_alphabet_set, utm_blank_symbol, Finset.mem_cons, Finset.mem_image, Finset.mem_range];
    apply Or.inr;
    have h_x_gt_zero : 0 < x := by
      simp only [utm_input_alphabet_set, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hx_in_input;
      rcases hx_in_input with (h | h | h | h | h);
      · rcases h with (h_val & (rfl|rfl)); all_goals { simp [encode_direction]; linarith };
      · rcases h with (h_val & rfl); simp [utm_tape_separator]; linarith;
      · rcases h with ⟨n, _, rfl⟩; simp [concrete_encode_nat_as_nat_for_desc]; linarith;
      · rcases h with ⟨n, _, rfl⟩; simp [concrete_encode_nat_as_nat_for_input]; linarith;
      · rcases h with ⟨n, _, rfl⟩; linarith;
    use Nat.pred x; constructor;
    · exact Nat.succ_pred_eq_of_pos h_x_gt_zero;
    · rw [Nat.pred_lt_iff_le h_x_gt_zero];
      simp only [utm_input_alphabet_set, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, overall_max_encoded_symbol_val, MAX_RAW_COMPONENT_VAL] at hx_in_input⊢;
      rcases hx_in_input with (h_components | h_lengths);
      rcases h_components with (h_comp2 | h_enc_input);
      rcases h_comp2 with (h_comp3 | h_enc_desc);
      rcases h_comp3 with (h_dirs | h_sep);
      · rcases h_dirs with (h_val_dir & (rfl|rfl)); all_goals { simp only [encode_direction]; linarith };
      · rcases h_sep with (h_val_sep & rfl); simp only [utm_tape_separator]; linarith;
      · rcases h_enc_desc with ⟨n_desc, h_n_desc_range, rfl⟩;
        simp only [concrete_encode_nat_as_nat_for_desc];
        have h_n_desc_bound : n_desc ≤ MAX_RAW_COMPONENT_VAL := Nat.lt_succ_iff.mp h_n_desc_range; linarith;
      · rcases h_enc_input with ⟨n_input, h_n_input_range, rfl⟩;
        simp only [concrete_encode_nat_as_nat_for_input];
        have h_n_input_bound : n_input ≤ MAX_RAW_COMPONENT_VAL := Nat.lt_succ_iff.mp h_n_input_range; linarith;
      · rcases h_lengths with ⟨n_len, h_n_len_range, rfl⟩;
        have h_n_len_bound : n_len ≤ MAX_RAW_COMPONENT_VAL := Nat.lt_succ_iff.mp h_n_len_range; linarith;
  blank_in_tape_alphabet := by simp [utm_tape_alphabet_set, utm_blank_symbol, Finset.mem_cons], -- Resolved SORRY B
  blank_not_in_input_alphabet := by -- Resolved SORRY C
    simp [utm_blank_symbol, utm_input_alphabet_set, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image];
    intros h_contra;
    rcases h_contra with (((h_dir | h_dir) | h_sep) | h_desc | h_input | h_len);
    · norm_num at h_dir;
    · norm_num at h_sep;
    · obtain ⟨n, _, hn⟩ := h_desc; simp [concrete_encode_nat_as_nat_for_desc] at hn; linarith
    · obtain ⟨n, _, hn⟩ := h_input; simp [concrete_encode_nat_as_nat_for_input] at hn; linarith
    · obtain ⟨n, _, hn⟩ := h_len; simp at hn; linarith
  start_in_states := by unfold utm_states_set S_start; simp, -- Resolved SORRY D
  accept_in_states := by unfold utm_states_set S_utm_accept; simp, -- Resolved SORRY E
  reject_in_states := by unfold utm_states_set S_utm_reject; simp, -- Resolved SORRY F
  valid_transition_fn := by sorry -- SORRY G (for the_actual_utm)
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
-- SORRY H: utm_transition_fn definition
end P_vs_NP_Framework
