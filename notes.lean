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

def Fee (chunk : List Tx) : Int := (map Tx.Fee chunk).foldl Int.add 0
def Size (chunk : List Tx) : Nat := Sum (map Size chunk)

structure FeeSize where
  fee : Int
  size : Nat
deriving Repr

def FeeSize.le (x y : FeeSize) : Prop :=
  (x.fee * y.size) ≤ (y.fee * x.size)

def FeeSize.same (x y : FeeSize) : Prop :=
  (x.fee * y.size) = (y.fee * x.size)

instance : LE FeeSize where
  le := FeeSize.le

instance dec_FeeSize_le : forall (x y : FeeSize), Decidable (x ≤ y) := by
  intro x y
  simp [LE.le,FeeSize.le]
  apply Int.decLe

def FeeSize.add (x y : FeeSize) : FeeSize :=
  FeeSize.mk (x.fee + y.fee) (x.size + y.size)

instance : Add FeeSize where
  add := FeeSize.add

def Price (l : List Tx) : FeeSize :=
  FeeSize.mk (Sum (map C.Fee l)) (Sum (map C.Size l))

mutual
  def StepFee (l : List FeeSize) : (List Rat) :=
    StepFee.steps 0 l
  def StepFee.steps (f : Rat) (l : List FeeSize) :=
    match l with
    | nil => [f]
    | h::t => StepFee.step1 f h t h.size
  def StepFee.step1 (f : Rat) (v : FeeSize) (l : List FeeSize) (left : Nat) :=
    match left with
    | 0 => StepFee.steps f l
    | left' + 1 => f::(StepFee.step1 (f + v.fee/v.size) v l left')
end
  termination_by StepFee.step1 _ _ l left => (l, left + 1); StepFee.steps f l => (l, 0)

def ListRat.le (a b : List Rat) : Prop :=
  match a, b with
  | nil, nil => True
  | ha::ta, hb::tb => (ha ≤ hb) ∧ (ListRat.le ta tb)
  | _, _ => False -- inconsistent sizes, incomparable

def Diagram (chunks : List (List Tx)) : List Rat :=
  StepFee (map Price chunks)

def Diagram.le (a b : List (List Tx)) : Prop :=
  ListRat.le (Diagram a) (Diagram b)



#eval Diagram [[(1,4),(2,3)],[(2,4)]]


def Diagram_Helper : FeeSize → List FeeSize → List FeeSize
  | x, [] => [x]
  | x, (y::zs) => match Diagram_Helper (x + y) zs with
    | [] => []
    | xyz::w => if (xyz < x) then x::(Diagram_Helper y zs) else (xyz::w)

def Improve_Step : List FeeSize → List FeeSize
  | [] => []
  | x::[] => [x]
  | x::y::z => if (x < y) then ((x+y)::z) else x::(Improve_Step (y::z))

def Improve_Helper : Nat → List FeeSize → List FeeSize
  | 0 => (fun l => l)
  | n+1 => (fun l => Improve_Helper n (Improve_Step l))

def WellOrdered : List FeeSize -> Prop
  | [] => True
  | _::[] => True
  | x::y::zz => (¬ x < y) ∧ WellOrdered (y::zz)

theorem improve_step_length: forall (l), (Improve_Step l).length = l.length ∨ (Improve_Step l).length + 1 = l.length := by
  intro l; induction l with
  | nil => simp [Improve_Step]
  | cons h t hind => cases t with
    | nil => simp [Improve_Step]
    | cons h2 t2 => 
      have hdec : Decidable (h < h2) := by exact dec_FeeSize_lt h h2 
      cases hdec with
      | isTrue hdec =>
        simp [hdec, Improve_Step]
      | isFalse hdec =>
        simp [hdec, Improve_Step]
        rw [List.length_cons, Nat.succ_eq_add_one] at hind
        apply Or.elim hind
        intro hind1
        apply Or.intro_left
        exact hind1
        intro hind2
        apply Or.intro_right
        apply Nat.add_right_cancel
        apply hind2

theorem improve_step_samelength: forall (l l'), l' = Improve_Step l → l.length = l'.length → l' = l := by
  intro l; induction l with
  | nil => simp [Improve_Step]; intro l' hl'; intros; exact hl'
  | cons h t hind => intro l' hl' hleneq; cases t with
    | nil => unfold Improve_Step at hl'; exact hl'
    | cons h' t' => unfold Improve_Step at hl';


theorem wo_no_improve: forall l, WellOrdered l → (Improve_Step l = l) := by
  intro l; induction l with
  | nil => simp [WellOrdered,Improve_Step]
  | cons h t hind => unfold WellOrdered; cases t with
    | nil => simp [Improve_Step]
    | cons h2 t2 => simp [Improve_Step]; intro hwo; simp [And.left hwo]; apply hind; apply And.right hwo

theorem iflteq: forall (t) (a b : FeeSize) (c d e : t), (if (a < b) then c else d) = e → (¬ c = e) → (¬ a < b) := by
  intro t a b c d e hif hneq hlt
  apply hneq
  rewrite [<-hif]
  simp [hlt]

theorem list_ht_eq_tail: forall (a b : T) (c d : List T), (a::c) = (b::d) -> c = d := by
  intro a b c d; simp; intro h; apply And.right h

theorem list_t_neq_cons_t: forall (t : List x) (h : x), t = (h::t) -> False := by
  intro t; induction t with
  | nil => simp
  | cons h t hind => intro h2; intro heq; apply hind h; apply list_ht_eq_tail; apply heq

theorem list_ht_neq_cons_ht: forall (t : List x) (a b c : x), a::t = (b::c::t) -> False := by
  intro t a b c; simp; intro heq; apply list_t_neq_cons_t; apply And.right heq

theorem list_cons: forall (a b : T) (c d), a::c = b::d -> (a = b /\ c = d) := by
  intro a b c d; simp; intro heq; apply heq

theorem and_a_ab: forall a b, a -> (a->b) -> a ∧ b := by
  intro a b ha hab; apply And.intro; trivial; apply hab; trivial

theorem no_improve_step_ex: forall (x y : FeeSize) (z a b c),
     (if (x < y) then (a::z) else (b::c)) = (x::y::z)
     -> (x < y -> False) ∧ b = x ∧ c = y::z := by
  intro x y z a b c hif
  apply and_a_ab; intro hxy; apply list_ht_neq_cons_ht z a x y; rw [<-hif]; simp [hxy]
  intro hxy; apply list_cons; rw [<-hif]; rw [if_neg]; apply hxy

theorem no_improve_step_tail: forall (b a), (Improve_Step (a::b)) = a::b -> Improve_Step b = b := by
  intro b a; cases b with
  | nil => simp [Improve_Step];
  | cons h t => simp [Improve_Step]; intro hif; apply (And.right (And.right (no_improve_step_ex _ _ _ _ _ _ hif)))

theorem no_improve_step_cond: forall (a b c), (Improve_Step (a::b::c)) = a::b::c -> (a < b -> False) := by
  intro a b c; simp [Improve_Step]; intro heq
  apply And.left (no_improve_step_ex _ _ _ _ _ _ heq)

theorem no_improve_wo: forall l, (Improve_Step l = l) -> WellOrdered l := by
  intro l; induction l with
  | nil => simp [WellOrdered,Improve_Step]
  | cons h t hind => unfold WellOrdered; cases t with
    | nil => simp [Improve_Step]
    | cons h2 t2 => simp; intro himp; apply And.intro; apply no_improve_step_cond; apply himp; apply hind; apply no_improve_step_tail; apply himp

*   



