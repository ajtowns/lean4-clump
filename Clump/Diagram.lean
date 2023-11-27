/- Support for "diagrams" */

import Init.Data.List.Basic
import Lean.Data.Rat           -- rational numbers
import Mathlib.Data.List.Perm  -- (l1 ~ l2) is true if list l2 is a permutation of list l1
import Std.Data.Rat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Linarith.Frontend

universe u

open List
open Rat

namespace Diagram

abbrev Diagram := List Rat

def le (a b : Diagram) : Prop :=
  match a, b with
  | nil, nil => True
  | ha::ta, hb::tb => (ha ≤ hb) ∧ (le ta tb)
  | _, _ => False -- inconsistent sizes, incomparable

def lt (a b : Diagram) : Prop :=
  match a, b with
  | nil, nil => True
  | ha::ta, hb::tb => (ha < hb) ∧ (lt ta tb)
  | _, _ => False -- inconsistent sizes, incomparable

instance : LE Diagram :=
  le := le

instance : LT Diagram :=
  lt := lt

instance dec_Diagram_le : forall (x y : Diagram), Decidable (x ≤ y) := by
  intro x; induction x with
  | nil => intro y; cases y; simp [Diagram.le]; exact decidableTrue; simp [Diagram.le]; exact decidableFalse
  | cons h t t_ih => intro y; cases y with
    | nil => simp [Diagram.le]; exact decidableFalse
    | cons yh yt => apply And.decidable

instance dec_Diagram_lt : forall (x y : Diagram), Decidable (x < y) := by
  intro x; induction x with
  | nil => intro y; cases y; simp [LT.lt]; exact decidableTrue; simp [LT.lt]; exact decidableFalse
  | cons h t t_ih => intro y; cases y with
    | nil => simp [LT.lt]; exact decidableFalse
    | cons yh yt => apply And.decidable

class DiagramCmp (α : Type u) where
  /-- Compare two chunkings by diagram (less than or equal) -/
  le : α → α → Prop
  /-- Compare two chunkings by diagram (strictly less than) -/
  lt : α → α → Prop

/-- Compare two chunkings by diagram (greater than or equal) -/
@[reducible] def DiagramCmp.ge {α : Type u} [DiagramCmp α] (a b : α) : Prop := DiagramCmp.le b a

/-- Compare two chunkings by diagram (strictly greater than) -/
@[reducible] def DiagramCmp.gt {α : Type u} [DiagramCmp α] (a b : α) : Prop := DiagramCmp.lt b a

end Diagram
