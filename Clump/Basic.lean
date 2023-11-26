import Init.Data.List.Basic
import Lean.Data.Rat           -- rational numbers
import Mathlib.Data.List.Perm  -- (l1 ~ l2) is true if list l2 is a permutation of list l1

universe u

open List
open Lean

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

section CluMP

-- This is the data we're working on
class HCluster (Tx : Type u) where
  parent : Tx -> Tx -> Prop
  parent_sensible : ∀ (p c : Tx), parent p c -> ¬ (RTC parent p c)
  Fee : Tx -> Int
  Size : Tx -> Nat
  zerosize_zerofee : ∀ (t : Tx), Size t = 0 -> Fee t = 0

variable {Tx : Type u} [HCluster Tx]
open HCluster

-- For messing about with #eval, we'll allow writing a tx as (fee, size)
@[default_instance]
instance : HCluster (Int × Nat) where
  parent := fun _ _ => False
  parent_sensible := by intros; contradiction
  Fee tx := if let Nat.succ _ := tx.2 then tx.1 else 0
  Size tx := tx.2
  zerosize_zerofee := by simp

#check Fee
#check (foldl Int.add 0)

def xFee (c : List Tx) : Int := foldl Int.add 0 (map Fee c)
def xSize (c : List Tx) : Nat := foldl Nat.add 0 (map Size c)

 -- structure FeeSize where
 --   fee : Int
 --   size : Nat
 -- deriving Repr
 --
 -- def FeeSize.le (x y : FeeSize) : Prop :=
 --   (x.fee * y.size) ≤ (y.fee * x.size)
 --
 -- def FeeSize.same (x y : FeeSize) : Prop :=
 --   (x.fee * y.size) = (y.fee * x.size)
 --
 -- instance : LE FeeSize where
 --   le := FeeSize.le
 --
 --instance dec_FeeSize_le : forall (x y : FeeSize), Decidable (x ≤ y) := by
 --  intro x y
 --  simp [LE.le,FeeSize.le]
 --  apply Int.decLe
 --
 --def FeeSize.add (x y : FeeSize) : FeeSize :=
 --  FeeSize.mk (x.fee + y.fee) (x.size + y.size)
 --
 --instance : Add FeeSize where
 --  add := FeeSize.add
 --
 --def Price (l : List Tx) : FeeSize :=
 --  FeeSize.mk (Sum (map C.Fee l)) (Sum (map C.Size l))
 --
 --mutual
 --  def StepFee (l : List FeeSize) : (List Rat) :=
 --    StepFee.steps 0 l
 --  def StepFee.steps (f : Rat) (l : List FeeSize) :=
 --    match l with
 --    | nil => [f]
 --    | h::t => StepFee.step1 f h t h.size
 --  def StepFee.step1 (f : Rat) (v : FeeSize) (l : List FeeSize) (left : Nat) :=
 --    match left with
 --    | 0 => StepFee.steps f l
 --    | left' + 1 => f::(StepFee.step1 (f + v.fee/v.size) v l left')
 --end
 --  termination_by StepFee.step1 _ _ l left => (l, left + 1); StepFee.steps f l => (l, 0)
 --
 --def ListRat.le (a b : List Rat) : Prop :=
 --  match a, b with
 --  | nil, nil => True
 --  | ha::ta, hb::tb => (ha ≤ hb) ∧ (ListRat.le ta tb)
 --  | _, _ => False -- inconsistent sizes, incomparable
 --
 --def Diagram (chunks : List (List Tx)) : List Rat :=
 --  StepFee (map Price chunks)
 --
 --def Diagram.le (a b : List (List Tx)) : Prop :=
 --  ListRat.le (Diagram a) (Diagram b)
 --
 --
 --
 --#eval Diagram [[(1,4),(2,3)],[(2,4)]]
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
