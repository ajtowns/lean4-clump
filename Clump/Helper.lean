/- Basic, general helpers that are probably better implemented somewhere
   else in the standard library -/

import Init.Data.List.Basic
import Mathlib.Data.Rat.Defs

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

