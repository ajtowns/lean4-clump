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
variable {Tx : Type u} [DecidableEq Tx] [Cluster Tx]
open Cluster

theorem Chunk.induct {P : List Tx -> Prop} : (forall (h : Tx), P [h]) -> (forall (h h2 : Tx) (t), P (h::h2::t)) -> forall (c : Chunk Tx), P c.val := by
  intro h1 hmany c; cases c with | mk v p => induction v with
  | nil => contradiction
  | cons h t t_ih => cases t with
    | nil => apply h1
    | cons h2 t2 => apply hmany

theorem Chunk.append_ok: forall (a b : Chunk Tx), a.val ++ b.val ≠ [] := by
  intro a; cases a with
  | mk val property => cases val with
    | nil => contradiction
    | cons h t => intro b; simp

def Chunk.append (a b : Chunk Tx) : Chunk Tx := ⟨ a.val ++ b.val, append_ok a b ⟩

instance : Append (Chunk Tx) where
  append := Chunk.append

/-- Compare arbitrary chunks by feerate -/

def Chunk.Fee (c : Chunk Tx) : Int := foldl Int.add 0 (map Cluster.Fee c.val)
def Chunk.Size (c : Chunk Tx) : Nat := foldl Nat.add 0 (map Cluster.Size c.val)
def Chunk.FeeRate (c : Chunk Tx) : Rat := c.Fee /. c.Size
def Chunk.Order (c : Chunk Tx) := (c.FeeRate, c.Size)

instance : Preorder (Chunk Tx) := Preorder.lift Chunk.Order

theorem chunk_le_rat_le: forall (a b : Chunk Tx), (a ≤ b) = (a.Order ≤ b.Order) := by
  intro a b; simp [LE.le]

theorem dec_Rat_le: forall (a b : Rat), Decidable (a ≤ b) := by
  intro a b; simp [LE.le]; apply Bool.decEq

theorem chunk_lt_rat_lt: forall (a b : Chunk Tx), (a < b) = (a.Order < b.Order) := by
  intro a b; simp [LT.lt]

instance dec_Feerate_le: forall (x y : Chunk Tx), Decidable (x ≤ y) := by
 intro x y; rw [chunk_le_rat_le]; apply Prod.instDecidableLE

instance dec_Feerate_lt : forall (x y : Chunk Tx), Decidable (x < y) := by
 intro x y; apply dec_Preorder_lt

end specific
end CluMP
