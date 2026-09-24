import Maledictus.Kernel

namespace Maledictus

/-!
# Finite dictionary literals and key views

This executable model records the deliberately small dictionary fragment accepted by the scalar
frontend. Literal Boolean keys normalize to integer keys, dynamic keys are refused, and inserting
an equal key replaces its value without moving its first insertion position. A call to `keys`
produces a distinct key-view value. The view supports iteration, length, and membership, but it is
not a sequence: indexing and slicing remain fail-closed.

The model does not claim general mutable Python dictionary semantics. The admitted frontend
fragment contains only finite dictionary literals and no dictionary mutation.
-/

inductive FiniteDictRawKey where
  | boolean (value : Bool)
  | integer (value : Int)
  | string (value : String)
  | bytes (value : List Nat)
  | dynamic
  deriving DecidableEq

inductive FiniteDictKey where
  | integer (value : Int)
  | string (value : String)
  | bytes (value : List Nat)
  deriving DecidableEq

def normalizeFiniteDictKey : FiniteDictRawKey -> Option FiniteDictKey
  | .boolean false => some (.integer 0)
  | .boolean true => some (.integer 1)
  | .integer value => some (.integer value)
  | .string value => some (.string value)
  | .bytes value => some (.bytes value)
  | .dynamic => none

structure FiniteDictEntry where
  key : FiniteDictKey
  value : String
  deriving DecidableEq

def replaceFiniteDictValue
    (entries : List FiniteDictEntry) (key : FiniteDictKey) (value : String) :
    List FiniteDictEntry :=
  entries.map fun entry => if entry.key == key then { entry with value } else entry

def insertFiniteDictEntry
    (entries : List FiniteDictEntry) (key : FiniteDictKey) (value : String) :
    List FiniteDictEntry :=
  if entries.any (fun entry => entry.key == key) then
    replaceFiniteDictValue entries key value
  else
    entries ++ [{ key, value }]

def buildFiniteDict (entries : List (FiniteDictKey × String)) : List FiniteDictEntry :=
  entries.foldl (fun result entry => insertFiniteDictEntry result entry.1 entry.2) []

structure FiniteDictKeyView where
  values : List FiniteDictKey
  deriving DecidableEq

def finiteDictKeys (entries : List FiniteDictEntry) : FiniteDictKeyView :=
  { values := entries.map (fun entry => entry.key) }

inductive FiniteDictKeyViewOperation where
  | iterate
  | length
  | contains (key : FiniteDictKey)
  | index (offset : Int)
  | slice (start stop step : Option Int)
  deriving DecidableEq

inductive FiniteDictKeyViewResult where
  | keys (values : List FiniteDictKey)
  | length (value : Nat)
  | truth (value : Bool)
  | refused
  deriving DecidableEq

def executeFiniteDictKeyView
    (view : FiniteDictKeyView) : FiniteDictKeyViewOperation -> FiniteDictKeyViewResult
  | .iterate => .keys view.values
  | .length => .length view.values.length
  | .contains key => .truth (view.values.contains key)
  | .index _ => .refused
  | .slice _ _ _ => .refused

theorem dynamic_finite_dict_key_is_refused :
    normalizeFiniteDictKey .dynamic = none := by
  rfl

theorem boolean_finite_dict_keys_normalize_to_integer_keys :
    normalizeFiniteDictKey (.boolean false) = normalizeFiniteDictKey (.integer 0) ∧
      normalizeFiniteDictKey (.boolean true) = normalizeFiniteDictKey (.integer 1) := by
  constructor <;> rfl

theorem singleton_finite_dict_keys_preserve_insertion_order
    (key : FiniteDictKey) (value : String) :
    (finiteDictKeys (buildFiniteDict [(key, value)])).values = [key] := by
  simp [finiteDictKeys, buildFiniteDict, insertFiniteDictEntry]

theorem duplicate_finite_dict_key_keeps_first_position_and_last_value
    (key other : FiniteDictKey) (first replacement otherValue : String)
    (different : other ≠ key) :
    buildFiniteDict [(key, first), (other, otherValue), (key, replacement)] =
      [{ key, value := replacement }, { key := other, value := otherValue }] := by
  have reverseDifferent : key ≠ other := Ne.symm different
  simp [buildFiniteDict, insertFiniteDictEntry, replaceFiniteDictValue,
    different, reverseDifferent]

theorem finite_dict_key_view_iteration_is_insertion_order
    (entries : List FiniteDictEntry) :
    executeFiniteDictKeyView (finiteDictKeys entries) .iterate =
      .keys (entries.map (fun entry => entry.key)) := by
  rfl

theorem finite_dict_key_view_length_is_finite_dict_length
    (entries : List FiniteDictEntry) :
    executeFiniteDictKeyView (finiteDictKeys entries) .length = .length entries.length := by
  simp [executeFiniteDictKeyView, finiteDictKeys]

theorem finite_dict_key_view_index_is_refused
    (view : FiniteDictKeyView) (offset : Int) :
    executeFiniteDictKeyView view (.index offset) = .refused := by
  rfl

theorem finite_dict_key_view_slice_is_refused
    (view : FiniteDictKeyView) (start stop step : Option Int) :
    executeFiniteDictKeyView view (.slice start stop step) = .refused := by
  rfl

end Maledictus
