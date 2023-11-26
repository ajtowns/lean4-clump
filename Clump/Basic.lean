import Init.Data.List.Basic
import Lean.Data.Rat           -- rational numbers
import Mathlib.Data.List.Perm  -- (l1 ~ l2) is true if list l2 is a permutation of list l1

universe u

open List

-- Some general helpers

namespace AJHelper
-- HSum allows us to write (Sum [a,b,c]) instead of a + b + c
class HSum (α : Type u) where
  zero : α
  add : α → α → α

def Sum [HSum α] (x : List α) : α :=
 match x with
 | nil => HSum.zero
 | h::t => HSum.add h (Sum t)

instance : HSum Nat where
  zero := 0
  add := Nat.add

instance : HSum Int where
  zero := 0
  add := Int.add

instance : Append (List α) where
  append := List.append
end AJHelper

open AJHelper

-- Reflexive transitive closure: allows us to define (ancestor := RTC parent)
inductive RTC {α : Sort u} (r : α → α → Prop) : α → α → Prop where
  /-- Reflexive closure, so all a's are included -/
  | refl : ∀ a, RTC r a a
  /-- If `r a b` then `r⁺ a b`. This is the base case of the transitive closure. -/
  | base  : ∀ a b, r a b → RTC r a b
  /-- The transitive closure is transitive. -/
  | trans : ∀ a b c, RTC r a b → RTC r b c → RTC r a c

namespace CluMP

-- This is the data we're working on
class HCluster (Tx : Type u) where
  parent : Tx -> Tx -> Prop
  parent_sensible : ∀ (p c : Tx), parent p c -> ¬ (RTC parent p c)
  Fee : Tx -> Int
  Size : Tx -> Nat
  zerosize_zerofee : ∀ (t : Tx), Size t = 0 -> Fee t = 0

open HCluster

section specific
variable {Tx : Type u} [HCluster Tx]

def ChunkFee (c : List Tx) : Int := foldl Int.add 0 (map Fee c)
def ChunkSize (c : List Tx) : Nat := foldl Nat.add 0 (map Size c)

/-- Compare two chunks by feerate (less than or equal) -/
def Feerate_le (a b : List Tx) : Prop :=
  (ChunkFee a) * (ChunkSize b) ≤ (ChunkFee b * ChunkSize a)

/-- Compare two chunks by feerate (strictly less than) -/
def Feerate_lt (a b : List Tx) : Prop :=
  (ChunkFee a) * (ChunkSize b) < (ChunkFee b * ChunkSize a)

/-- Compare two chunks by feerate (greater than or equal) -/
@[reducible] def Feerate_ge (a b : List Tx) : Prop := Feerate_le b a

/-- Compare two chunks by feerate (strictly greater than) -/
@[reducible] def Feerate_gt (a b : List Tx) : Prop := Feerate_lt b a

@[inherit_doc] infix:50 " ≤$ "  => Feerate_le
@[inherit_doc] infix:50 " <$ "  => Feerate_lt
@[inherit_doc] infix:50 " ≥$ "  => Feerate_ge
@[inherit_doc] infix:50 " >$ "  => Feerate_gt

instance dec_Feerate_le : forall (x y : List Tx), Decidable (x ≤$ y) := by
 intro x y
 simp [LE.le,Feerate_le]
 apply Int.decLe

instance dec_Feerate_lt : forall (x y : List Tx), Decidable (x <$ y) := by
 intro x y
 simp [LT.lt,Feerate_lt]
 apply Int.decLt

mutual
  def Diagram (l : List (List Tx)) : (List Rat) :=
    Diagram.steps 0 l
  def Diagram.steps (f : Rat) (l : List (List Tx)) :=
    match l with
    | nil => [f]
    | h::t => Diagram.step1 f ((ChunkFee h)/(ChunkSize h)) t (ChunkSize h)
  def Diagram.step1 (f : Rat) (fpb : Rat) (l : List (List Tx)) (left : Nat) :=
    match left with
    | 0 => Diagram.steps f l
    | left' + 1 => f::(Diagram.step1 (f + fpb) fpb l left')
end
  termination_by Diagram.step1 _ _ l left => (l.length, left + 1); Diagram.steps _ l => (l.length, 0)

def ListRat.le (a b : List Rat) : Prop :=
  match a, b with
  | nil, nil => True
  | ha::ta, hb::tb => (ha ≤ hb) ∧ (ListRat.le ta tb)
  | _, _ => False -- inconsistent sizes, incomparable

def ListRat.lt (a b : List Rat) : Prop :=
  match a, b with
  | nil, nil => True
  | ha::ta, hb::tb => (ha < hb) ∧ (ListRat.lt ta tb)
  | _, _ => False -- inconsistent sizes, incomparable

instance dec_ListRat_le : forall (x y : List Rat), Decidable (ListRat.le x y) := by
  intro x; induction x with
  | nil => intro y; cases y; simp [ListRat.le]; exact decidableTrue; simp [ListRat.le]; exact decidableFalse
  | cons h t t_ih => intro y; cases y with
    | nil => simp [ListRat.le]; exact decidableFalse
    | cons yh yt => apply And.decidable

instance dec_ListRat_lt : forall (x y : List Rat), Decidable (ListRat.lt x y) := by
  intro x; induction x with
  | nil => intro y; cases y; simp [ListRat.lt]; exact decidableTrue; simp [ListRat.lt]; exact decidableFalse
  | cons h t t_ih => intro y; cases y with
    | nil => simp [ListRat.lt]; exact decidableFalse
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

/-- Provides ≤d notation for diagram comparison -/
instance : DiagramCmp (List (List Tx)) where
  le (a b : List (List Tx)) := ListRat.le (Diagram a) (Diagram b)
  lt (a b : List (List Tx)) := ListRat.lt (Diagram a) (Diagram b)

instance dec_Diagram_le : forall (x y : List (List Tx)), Decidable (DiagramCmp.le x y) := by
  intro x y; simp [DiagramCmp.le]; apply dec_ListRat_le

instance dec_Diagram_lt : forall (x y : List (List Tx)), Decidable (DiagramCmp.lt x y) := by
  intro x y; simp [DiagramCmp.lt]; apply dec_ListRat_lt

@[inherit_doc] infix:50 " ≤d "  => DiagramCmp.le
@[inherit_doc] infix:50 " <d "  => DiagramCmp.lt
@[inherit_doc] infix:50 " ≥d "  => DiagramCmp.ge
@[inherit_doc] infix:50 " >d "  => DiagramCmp.gt

 --
 --
 --def Diagram_Helper : FeeSize → List FeeSize → List FeeSize
 --  | x, [] => [x]
 --  | x, (y::zs) => match Diagram_Helper (x + y) zs with
 --    | [] => []
 --    | xyz::w => if (xyz < x) then x::(Diagram_Helper y zs) else (xyz::w)
 --
 --def Improve_Step : List FeeSize → List FeeSize
 --  | [] => []
 --  | x::[] => [x]
 --  | x::y::z => if (x < y) then ((x+y)::z) else x::(Improve_Step (y::z))
 --
 --def Improve_Helper : Nat → List FeeSize → List FeeSize
 --  | 0 => (fun l => l)
 --  | n+1 => (fun l => Improve_Helper n (Improve_Step l))
 --
 --def WellOrdered : List FeeSize -> Prop
 --  | [] => True
 --  | _::[] => True
 --  | x::y::zz => (¬ x < y) ∧ WellOrdered (y::zz)
 --

end specific
end CluMP
