/- Handling feerates of a List of Txs in a Cluster -/

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

universe u

open List
open Rat
open CluMP
open AJHelper

namespace CluMP

section specific
variable {Tx : Type u} [Cluster Tx]
open Cluster

/-- Compare arbitrary chunks by feerate -/

def ChunkFee (c : List Tx) : Int := foldl Int.add 0 (map Fee c)
def ChunkSize (c : List Tx) : Nat := foldl Nat.add 0 (map Size c)
def ChunkFeeRate (c : List Tx) : Rat := (ChunkFee c) /. (ChunkSize c)
def ChunkOrder (c : List Tx) := (ChunkFeeRate c, ChunkSize c)

instance : Preorder (List Tx) := Preorder.lift ChunkOrder

@[simp]
theorem chunk_le_rat_le: forall (a b : List Tx), (a ≤ b) = ((ChunkOrder a) ≤ (ChunkOrder b)) := by
  intro a b; simp [LE.le]

theorem dec_Rat_le: forall (a b : Rat), Decidable (a ≤ b) := by
  intro a b; simp [LE.le]; apply Bool.decEq

@[simp]
theorem chunk_lt_rat_lt: forall (a b : List Tx), (a < b) = ((ChunkOrder a) < (ChunkOrder b)) := by
  intro a b; simp [LT.lt]

instance dec_Feerate_le: forall (x y : List Tx), Decidable (x ≤ y) := by
 intro x y; rw [chunk_le_rat_le]; apply Prod.instDecidableLE

instance dec_Feerate_lt : forall (x y : List Tx), Decidable (x < y) := by
 intro x y; apply dec_Preorder_lt

end specific
end CluMP
