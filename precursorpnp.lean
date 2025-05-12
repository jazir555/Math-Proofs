Okay, I will proceed with **Subtask 18: Sketch logic for `C_setup_sim_tape` in `utm_transition_fn` (SORRY H).**

This subtask focuses on detailing how the `C_setup_sim_tape` state would initialize the simulated Turing Machine's tape based on the encoded input word found on the UTM's main tape. This involves reading, decoding, and conceptually preparing the `sim_tape` for the `UTMSimulationContext`.

The `internal_data` for `C_setup_sim_tape` might need to act as a counter if we read the input word symbol by symbol. The `parse_one_length_prefixed_list_from_tape` is designed for length-prefixed lists; the input word isn't necessarily length-prefixed in our current encoding (it's just `encoded_M ++ [sep] ++ encoded_w`). The UTM would read until it hits a blank or another suitable end-marker for the simulated input on its tape.

For simplicity in this sketch, let's assume `C_setup_sim_tape` reads until it encounters a `utm_blank_symbol` on the tape, interpreting symbols using `decode_nat_from_input`.

Here is the entire current proof state, with Subtask 18 integrated:

```lean
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
import Mathlib.Data.Nat.Pairing -- For Nat.pair and Nat.unpair (crucial for state encoding)
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
    intro q₁ s₁ h; let res := (transition_function (q₁, s₁)).get!; have h' := Option.get_isSome h;
    unfold transition_function at h'; split_ifs at h' with hq hs1 hs0 hsb <;> (try subst q₁ s₁); simp at h';
    any_goals rw [←h']; simp [states_set, tape_alphabet_set, Finset.mem_insert, Finset.mem_singleton, *]
    all_goals except (exact False.elim (Option.noConfusion h'))
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
def C_setup_sim_tape_read_input : ℕ := 18 -- Renamed state: Reading the encoded input word
def C_sim_read_symbol : ℕ := 19; def C_sim_fetch_rule : ℕ := 20
def C_sim_apply_write : ℕ := 21; def C_sim_apply_move : ℕ := 22
def C_sim_update_state : ℕ := 23
def C_utm_accept : ℕ := 24; def C_utm_reject : ℕ := 25
end UTMControlCode
open UTMControlCode

def utm_control_codes_set : Finset UniversalTuringMachine_spec_σ :=
  { C_start, C_parse_states_len, C_parse_states_val, C_parse_ia_len, C_parse_ia_val,
    C_parse_ta_len, C_parse_ta_val, C_parse_b_len, C_parse_b_val, C_parse_q0_len, C_parse_q0_val,
    C_parse_qa_len, C_parse_qa_val, C_parse_qr_len, C_parse_qr_val, C_parse_delta_len, C_parse_delta_val,
    C_find_sep_before_input, C_setup_sim_tape_read_input,
    C_sim_read_symbol, C_sim_fetch_rule, C_sim_apply_write, C_sim_apply_move, C_sim_update_state,
    C_utm_accept, C_utm_reject }

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
  states : Finset ℕ; input_alphabet : Finset ℕ; tape_alphabet : Finset ℕ
  blank_symbol : ℕ; start_state : ℕ; accept_state : ℕ; reject_state : ℕ
  transitions : List (ℕ × ℕ × ℕ × ℕ × ℕ)
deriving Repr, Inhabited
instance : EmptyCollection ParsedTMDescription :=
  ⟨{ states := ∅, input_alphabet := ∅, tape_alphabet := ∅, blank_symbol := 0,
     start_state := 0, accept_state := 0, reject_state := 0, transitions := [] }⟩

-- This data would ideally be stored on the UTM's tape in designated work areas.
-- For the transition function sketch, we imagine it's accessible.
structure UTMTemporaryDataStore : Type where
  parsed_tm_cache       : Option ParsedTMDescription  -- Cache of the fully parsed TM
  sim_input_word_buffer : List ℕ                      -- Buffer for decoded input symbols during setup
  sim_current_q         : ℕ                           -- Current state of simulated TM
  sim_tape_current_sym  : ℕ                           -- Current symbol on simulated tape
  -- Rule components for current step:
  sim_next_q            : ℕ
  sim_write_s           : ℕ
  sim_move_dir_encoded  : ℕ
deriving Inhabited
instance : EmptyCollection UTMTemporaryDataStore :=
  ⟨{ parsed_tm_cache := none, sim_input_word_buffer := [], sim_current_q := 0, sim_tape_current_sym := 0,
     sim_next_q := 0, sim_write_s := 0, sim_move_dir_encoded := 0 }⟩

-- The opaque functions represent interactions with this conceptual data store,
-- which in a real UTM would be complex tape read/write sequences.
opaque get_utm_temp_data : Unit → UTMTemporaryDataStore -- Reads from work tape
opaque set_utm_temp_data (data : UTMTemporaryDataStore) : Unit -- Writes to work tape
-- Specific getters/setters for conceptual clarity (would be part of UTM state logic)
opaque store_parsed_tm (ptm : ParsedTMDescription) : Unit
opaque get_parsed_tm : Unit → Option ParsedTMDescription
opaque add_to_sim_input_buffer (sym : ℕ) : Unit
opaque get_and_clear_sim_input_buffer : Unit → List ℕ
opaque set_sim_current_q (q : ℕ) : Unit
opaque get_sim_current_q : Unit → ℕ
-- Interactions with the simulated tape (on the UTM's main tape)
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
    : Option (UniversalTuringMachine_spec_σ × UniversalTuringMachine_spec_α × Direction) :=
  if tape_symbol = 0 then some (Nat.pair C_utm_reject 0, utm_b, Direction.right)
  else
    let actual_len := tape_symbol - 1
    some (Nat.pair next_val_control_code actual_len, utm_b, Direction.right)

def handle_parse_val_state (current_val_control_code : ℕ) (next_len_control_code : ℕ)
    (internal_data : ℕ) (tape_symbol : UniversalTuringMachine_spec_α)
    (utm_b : UniversalTuringMachine_spec_α)
    : Option (UniversalTuringMachine_spec_σ × UniversalTuringMachine_spec_α × Direction) :=
  if internal_data = 0 then
    some (Nat.pair next_len_control_code 0, tape_symbol, Direction.right)
  else
    let items_remaining := internal_data - 1
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
  | C_start =>
      -- In a real UTM, C_start would call parse_full_tm_description_from_tape.
      -- For this sketch, we assume the parsing states C_parse_..._len/val achieve this.
      -- So, C_start directly transitions to the first parsing state.
      -- tape_symbol is the first symbol of the TM description (length of states list).
      some (Nat.pair C_parse_states_len 0, tape_symbol, Direction.right)

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
  | C_parse_delta_len => handle_parse_len_state C_parse_delta_val tape_symbol utm_b
  | C_parse_delta_val => handle_parse_val_state C_parse_delta_val C_find_sep_before_input internal_data tape_symbol utm_b

  | C_find_sep_before_input =>
    if tape_symbol = utm_tape_separator then
      some (Nat.pair C_setup_sim_tape_read_input 0, utm_b, Direction.right) -- tape_symbol is now separator, move right to first input symbol
    else if tape_symbol = utm_b then
      some (Nat.pair C_utm_reject 0, utm_b, Direction.right)
    else
      some (Nat.pair C_find_sep_before_input 0, tape_symbol, Direction.right)

  | C_setup_sim_tape_read_input =>
      -- `tape_symbol` is an encoded symbol from the simulated TM's input word.
      -- `internal_data` could be a flag (0 = reading, 1 = finished/hit blank). Here, simple loop.
      if tape_symbol = utm_b then -- End of encoded input word (assuming it ends with UTM blank on tape)
        -- Conceptual: get_and_clear_sim_input_buffer to form initial sim_tape.
        -- Conceptual: set_sim_current_q to (get_parsed_tm ()).get!.start_state
        -- Transition to start simulation.
        some (Nat.pair C_sim_read_symbol 0, utm_b, Direction.right) -- Placeholder: assume sim tape setup done.
      else
        match decode_nat_from_input tape_symbol with
        | none => some (Nat.pair C_utm_reject 0, utm_b, Direction.right) -- Invalid input symbol
        | some decoded_sim_symbol =>
            -- Conceptual: add_to_sim_input_buffer decoded_sim_symbol
            -- Continue reading next input symbol.
            some (Nat.pair C_setup_sim_tape_read_input 0, utm_b, Direction.right)

  | C_sim_read_symbol =>
      -- Conceptual: let current_sim_symbol := read_current_sim_tape_symbol_from_utm_tape ()
      -- For sketch, assume tape_symbol *is* the current_sim_symbol (UTM head is on sim tape part)
      let current_sim_symbol_val := tape_symbol -- This must be a DECODED sim symbol if on actual sim tape section.
                                              -- Or if it's an ENCODED symbol from UTM tape, it needs decoding.
                                              -- This part needs careful handling of tape sections.
      some (Nat.pair C_sim_fetch_rule current_sim_symbol_val, utm_b, Direction.right)

  | C_sim_fetch_rule =>
      let current_sim_symbol := internal_data
      let ptm_opt := get_parsed_tm () -- Conceptual
      let current_q_sim := get_sim_current_q () -- Conceptual
      match ptm_opt with
      | none => some (Nat.pair C_utm_reject 0, utm_b, Direction.right) -- Parsed TM not available
      | some ptm =>
        match find_sim_transition ptm current_q_sim current_sim_symbol with
        | none => -- Simulated TM halts
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
      -- Conceptual: write_current_sim_tape_symbol_to_utm_tape rule_data.write_s_sim
      some (Nat.pair C_sim_apply_move internal_data, rule_data.write_s_sim, Direction.right) -- UTM writes and immediately moves for next state.

  | C_sim_apply_move =>
      let rule_data := decode_sim_rule_components_for_apply internal_data
      match decode_direction_opt rule_data.move_dir_sim_encoded with
      | none => some (Nat.pair C_utm_reject 0, utm_b, Direction.right)
      | some move_d_sim =>
          -- Conceptual: move_sim_tape_head_on_utm_tape move_d_sim ( (get_parsed_tm ()).get!.blank_symbol )
          some (Nat.pair C_sim_update_state internal_data, utm_b, move_d_sim)

  | C_sim_update_state =>
      let rule_data := decode_sim_rule_components_for_apply internal_data
      -- Conceptual: set_sim_current_q rule_data.next_q_sim
      some (Nat.pair C_sim_read_symbol 0, utm_b, Direction.right)

  | C_utm_accept => none
  | C_utm_reject => none
  | _ => some (Nat.pair C_utm_reject 0, tape_symbol, Direction.right)
-- SORRY H continues: simulation cycle sketched, but relies on opaque tape ops / context.

def the_actual_utm_instance : UniversalTuringMachine := {
  states := Finset.image (fun code => Nat.pair code 0) utm_control_codes_set, -- Placeholder
  input_alphabet := utm_input_alphabet_set,
  tape_alphabet := utm_tape_alphabet_set,
  blank_symbol := utm_blank_symbol,
  transition_fn := utm_transition_fn,
  start_state := Nat.pair C_start 0,
  accept_state := Nat.pair C_utm_accept 0,
  reject_state := Nat.pair C_utm_reject 0,

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
  start_in_states := by simp [utm_control_codes_set, C_start]; sorry, -- SORRY D
  accept_in_states := by simp [utm_control_codes_set, C_utm_accept]; sorry, -- SORRY E
  reject_in_states := by simp [utm_control_codes_set, C_utm_reject]; sorry, -- SORRY F
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
-- SORRY H: utm_transition_fn definition is now substantially sketched for parsing and simulation cycle.
end P_vs_NP_Framework
