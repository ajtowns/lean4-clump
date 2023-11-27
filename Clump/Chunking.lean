/- Deal with gathering txs into chunks */

import Init.Data.List.Basic
import Lean.Data.Rat           -- rational numbers
import Mathlib.Data.List.Perm  -- (l1 ~ l2) is true if list l2 is a permutation of list l1
import Std.Data.Rat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Linarith.Frontend

import Clump.Helper
import Clump.Basic
import Clump.Feerate
import Clump.Diagram

universe u

open List
open Rat

namespace CluMP

section specific
variable {Tx : Type u} [Cluster Tx]
open Cluster
open Diagram

abbrev Chunking := List (List Tx)

mutual
  def Diagram (l : Chunking) : (List Rat) :=
    Diagram.steps 0 l
  def Diagram.steps (f : Rat) (l : Chunking) :=
    match l with
    | nil => [f]
    | h::t => Diagram.step1 f ((ChunkFee h)/(ChunkSize h)) t (ChunkSize h)
  def Diagram.step1 (f : Rat) (fpb : Rat) (l : Chunking) (left : Nat) :=
    match left with
    | 0 => Diagram.steps f l
    | left' + 1 => f::(Diagram.step1 (f + fpb) fpb l left')
end
  termination_by Diagram.step1 _ _ l left => (l.length, left + 1); Diagram.steps _ l => (l.length, 0)

/-- Provides ≤d notation for diagram comparison -/
instance : LE Chunking where
  le (a b : Chunking) := (Diagram a) ≤ (Diagram b)

instance : LT Chunking where
  lt (a b : Chunking) := (Diagram a) < (Diagram b)

instance dec_Diagram_le : forall (x y : Chunking), Decidable (x ≤ y) := by
  intro x y; simp [LE.le]; apply dec_ListRat_le

instance dec_Diagram_lt : forall (x y : Chunking), Decidable (x < y) := by
  intro x y; simp [LT.lt]; apply dec_ListRat_lt

def Chunk.merge_back (next : (List Tx)) (back : (Chunking)) :=
  match back with
   | [] => [next]
   | check::back' => if (check < next) then (Chunk.merge_back (check ++ next) back') else next::check::back'

def Chunk.helper (fin todo : Chunking) :=
  match todo with
  | [] => fin.reverse
  | chunk::todo' => Chunk.helper (Chunk.merge_back chunk fin) todo'

def Chunk.raise (c : List Tx) := map (fun el => [el]) c

/-- Implements chunking in linear time -/
def Chunk (l : List Tx) : Chunking :=
  Chunk.helper [] (Chunk.raise l)

end specific
end CluMP
