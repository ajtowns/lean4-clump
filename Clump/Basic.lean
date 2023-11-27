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

-- abbrev ??? := List Tx      (Chunk? Linearisation? ...?)
-- abbrev Diagram := List Rat

/-- Compare arbitrary chunks by feerate -/

def ChunkFee (c : List Tx) : Int := foldl Int.add 0 (map Fee c)
def ChunkSize (c : List Tx) : Nat := foldl Nat.add 0 (map Size c)
def ChunkFeeRate (c : List Tx) : Rat := (ChunkFee c) /. (ChunkSize c)
def ChunkOrder (c : List Tx) := (ChunkFeeRate c, ChunkSize c)

theorem divNat_one: forall (c : Nat), ↑c = c/.1 := by
  intro c; rw [divInt_one]; simp

instance dec_And {a b} [Ha: Decidable a] [Hb: Decidable b] : Decidable (a ∧ b) := by
  cases Ha with
  | isFalse Ha => left; simp; intro; contradiction
  | isTrue Ha => cases Hb with
    | isFalse Hb => left; simp [Hb]
    | isTrue Hb => right; simp [Ha,Hb]

instance dec_Preorder_lt {α : Type u} [Preorder α] [decle: @DecidableRel α (· ≤ ·)]: @DecidableRel α (· < ·) :=
  by intro a b; simp; rw [lt_iff_le_not_le]; apply dec_And

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


def Chunk.merge_back (next : (List Tx)) (back : (List (List Tx))) :=
  match back with
   | [] => [next]
   | check::back' => if (check < next) then (Chunk.merge_back (check ++ next) back') else next::check::back'

def Chunk.helper (fin todo : List (List Tx)) :=
  match todo with
  | [] => fin.reverse
  | chunk::todo' => Chunk.helper (Chunk.merge_back chunk fin) todo'

def Chunk.raise (c : List Tx) := map (fun el => [el]) c

/-- Implements chunking in linear time -/
def Chunk (l : List Tx) : List (List Tx) :=
  Chunk.helper [] (Chunk.raise l)




def Monotonic {α : Type u} (r : α → α → Prop) (l : List α) : Prop :=
  match l with
  | nil => True
  | _::nil => True
  | a::b::t => r a b ∧ Monotonic r (b::t)

def Monotonic.rev {α : Type u} (r : α → α → Prop) (l : List α) : Prop :=
 match l with
 | nil => True
 | _::nil => True
 | a::b::t => r b a ∧ Monotonic.rev r (b::t)

theorem Monotonic_rev_of_reverseAux: forall (r) (a : List α) (b c d), Monotonic r (b::a) -> Monotonic.rev r (d::c) -> r d b -> Monotonic.rev r (reverseAux (b::a) (d::c)) := by
  intro r a; induction a with
  | nil => intro b c d _ Hdc Hdb; simp [reverseAux,Monotonic.rev]; exact {left := Hdb, right := Hdc}
  | cons ha ta at_ih => intros b c d Hba Hdc Hdb; rw [reverseAux]; apply at_ih; simp [Monotonic] at Hba; apply Hba.right; simp [Monotonic.rev,Hdc,Hdb]; simp [Monotonic] at Hba; apply Hba.left

theorem Monotonic_rev_of_reverse_mp: forall (r) (l : List α), Monotonic r l → Monotonic.rev r (l.reverse) := by
  intro r l; induction l with
  | nil => simp [Monotonic,Monotonic.rev]
  | cons h t t_ih => intros Ha; cases t with
    | nil => simp [Monotonic.rev]
    | cons h2 t2 => unfold reverse; rw [reverseAux]; apply Monotonic_rev_of_reverseAux; simp [Monotonic] at Ha; apply Ha.right; simp [Monotonic.rev]; simp [Monotonic] at Ha; apply Ha.left

theorem Monotonic_app3: forall (r) (a b c : List α), (¬ b = []) → Monotonic r (a++b) → Monotonic r (b++c) → Monotonic r (a++b++c) := by
  intros r a; induction a with
  | nil => intros b c _ _ Hbc; rw [nil_append]; exact Hbc
  | cons ha ta ta_ih => intros b c Hb Hab Hbc; rw [append_assoc, cons_append]; cases ta with
    | nil => cases b with
      | nil => contradiction
      | cons hb tb => simp [Monotonic]; simp [Monotonic] at Hab; apply And.intro; apply Hab.left; rw [<-cons_append]; exact Hbc
    | cons ha2 ta2 => simp; rw [<-append_assoc]; simp [Monotonic]; simp [Monotonic] at Hab; apply And.intro; apply Hab.left; rw [<-append_assoc]; apply ta_ih; exact Hb; rw [cons_append]; apply Hab.right; apply Hbc

/-- without loss of generality "tactic" so i don't repeat myself too much -/
theorem wlog {α β : Type u} (P : α → α → Prop) [hP : @DecidableRel α P] (Q : β -> Prop) (X : α → α → β) :
  (forall (a b), P a b -> Q (X a b)) -> (forall (a b), ¬ P a b -> P b a) -> forall (a b), Q (if (P a b) then X a b else X b a) := by
  intro hPQ hnP a b; have hPab : Decidable (P a b); apply hP; cases hPab with
  | isFalse hPab => simp [hPab]; apply hPQ; apply hnP; exact hPab
  | isTrue hPab => simp [hPab]; apply hPQ; apply hPab

/--
 Layout is:
    Cluster -- gives all the types and underlying representations
    abbrev Chunking := List (List Tx)
    abbrev Diagram := List Rat

    PartialOrder (List Tx) -- compare by feerate

    Raise : List Tx -> Chunking   -- raise each tx into [tx]
    Diagram : Chunking -> Diagram
    Optimise : Chunking -> Chunking
    Drop : Chunking -> List Tx    -- concatenate the chunks

    -- does Optimise [] return [] or [[]] ? does a Chunking ever have empty lists as elements?

    Reorder (chunk other : List Tx) : List Tx -- reorder "chunk" to be in "other" order

    PartialOrder Chunking  -- compare by diagram

    theorems:
      Perm (Reorder a o) a -- Reordering just reorders
      Drop (Raise a) = a
      Drop (Optimise a) = Drop a  -- order preserving
      (Optimise a) >= a
      (Optimise (Raise (Drop a))) >= a
      Optimise (a ++ b) = Optimise ((Optimise a) ++ (Optimise b))
      Optimise ((Optimise a) ++ b) = Optimise (a ++ b)
      Optimise (a ++ (Optimise b)) = Optimise (a ++ b)

      -- if a particular set of txs is the first chunk, optimising just those txs generates the same chunk
      Optimise a = h::t -> Optimise [Raise h] = [h]

      -- reordering a chunk only improves things
      Optimise a = [[Drop a]] -> Perm (Drop a) (Drop b) -> Optimise b >= Optimise (Raise a)

    pim-first base cmp:
      Reorder (head (Optimise (Raise base))) cmp



    prefix-intersection-merge:
      L1, L2 : List Tx
      HPerm : Perm L1 L2

      c1 = pim-first L1 L2
      c2 = pim-first L2 L1

      if (c1 >= c2) then
        (c1::prefix-intersection-merge (L1-c1) (L2-c1))
      else
        (c2::prefix-intersection-merge (L1-c2) (L2-c2))

 oops, this is a docstring so better follow it up with something
 -/
theorem trivial: False -> True := by intro Hf; cases Hf

-- theorem chunk_back_Monotonic: forall (lch) (ch : List Tx), Monotonic DiagramCmp.le lch -> Monotonic DiagramCmp.le (Chunk.chunk_back ch lch) := by
--  sorry

-- theorem Chunk_Monotonic: forall (l), Monotonic DiagramCmp.gt (Chunk l) := by

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
