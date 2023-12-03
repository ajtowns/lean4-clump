/- Support for "diagrams" -/

import Init.Data.List.Basic
import Mathlib.Data.List.Perm  -- (l1 ~ l2) is true if list l2 is a permutation of list l1
import Mathlib.Tactic.Linarith.Frontend

import Clump.Helper

universe u

open List

namespace Diagram

class Diagram (F : Type u) [LinearOrderedField F]

section specific
variable {F : Type u} [LinearOrderedField F]
variable [D : Diagram F]
variable [FdecLE : @DecidableRel F (· ≤ ·)]

inductive le : List F -> List F -> Prop where
  | empty : le [] []
  | step {h1 h2 : F} {t1 t2 : List F} : (h1 ≤ h2) -> (le t1 t2) -> le (h1::t1) (h2::t2)

instance : LE (List F) where
  le := le

instance decLE : forall (x y : List F), Decidable (x ≤ y) := by
  intro x; induction x with
  | nil => intro y; cases y; right; simp [LE.le]; exact le.empty; left; by_contra Hcontra; cases Hcontra
  | cons hx tx tx_ih => intro y; cases y with
    | nil => left; by_contra Hcontra; cases Hcontra
    | cons hy ty => simp [LE.le]; cases tx_ih ty with
      | isFalse Hf => left; by_contra Hcons; cases Hcons; contradiction
      | isTrue Htailok => cases (FdecLE hx hy) with
        | isFalse Hf => left; intro Hcontra; cases Hcontra; apply Hf; simp; assumption
        | isTrue Hheadok => right; simp at Hheadok; constructor; assumption; assumption

theorem le_nil_left: forall {a : List F}, [] ≤ a → a = [] := by
  intros a Ha; cases Ha with | empty => trivial
 
theorem le_nil_right: forall {a : List F}, a ≤ [] → a = [] := by
  intros a Ha; cases Ha with | empty => trivial

@[simp]
theorem le_cons: forall (h1 h2 : F) (t1 t2 : List F), (h1::t1) ≤ (h2::t2) ↔ (h1 ≤ h2 ∧ t1 ≤ t2) := by
  intros; constructor; intros Ha; cases Ha; constructor; assumption; assumption
  apply and_imp_to_imp_imp; intros Hh Ht; constructor; assumption; assumption

@[simp]
theorem le_app_left_same: forall (a b c d : List F), a ≤ c → b ≤ d → (a ++ b) ≤ (c ++ d) := by
  intro a; induction a with
  | nil => intro b c d Hac Hbd; apply le_nil_left at Hac; rw [Hac]; simp; assumption
  | cons h t t_ih => intro b c d Hac Hbd; cases c with
    | nil => contradiction
    | cons ch ct => cases Hac with | step Hh Ht => constructor; assumption; apply t_ih; assumption; assumption

def bump (a : List F) (n : F) : List F := map (fun el => n + el) a

theorem bump_nil: forall (n : F), bump [] n = [] := by
  intros; simp [bump, map]

theorem bump_by_0: forall (a : List F), bump a 0 = a := by
  intro a; simp [bump]

theorem bump_ht: forall (h n : F) t, bump (h::t) n = (n+h)::(bump t n) := by
  intros; simp [bump, map]

theorem bump_to_nil: forall (n : F) a, bump a n = [] -> a = [] := by
  intros n a Hb; cases a with
  | nil => trivial
  | cons h t => rw [bump_ht] at Hb; contradiction

theorem bump_le_n_le: forall (a1 a2 : List F) n1 n2, a1 ≤ a2 → n1 ≤ n2 → (bump a1 n1) ≤ (bump a2 n2) := by
  intros a1; induction a1 with
  | nil => intros a2 n1 n2 Ha _; apply le_nil_left at Ha; rw [Ha, bump_nil, bump_nil]; exact le.empty
  | cons a1h a1t a1t_ih => intro a2 n1 n2 Ha Hn; cases a2 with
    | nil => contradiction
    | cons a2h a2t => rw [bump_ht]; cases Ha with 
      | step Hh Ht => constructor; simp; apply add_le_add Hn; assumption; apply a1t_ih; assumption; assumption

theorem bump_le: forall (a b : List F) n, (bump a n) ≤ (bump b n) ↔ a ≤ b := by
  intro a; induction a with
  | nil => intro b n; simp [bump_nil]; constructor
           intro Hbump; apply le_nil_left at Hbump; apply bump_to_nil at Hbump; rw [Hbump]; apply le.empty
           intro Hb; apply le_nil_left at Hb; rw [Hb, bump_nil]; apply le.empty
  | cons h t t_ih =>
           intro b n; constructor
           intro Hbump; cases b with
           | nil => rw [bump_nil,bump_ht] at Hbump; apply le_nil_right at Hbump; contradiction
           | cons hb tb => rw [bump_ht] at Hbump; cases Hbump with
             | step => revert n; intro n Hh Ht; simp at Hh; constructor; assumption
                       apply (t_ih tb n).mp; assumption
           intro Hle; cases b with
           | nil => apply le_nil_right at Hle; contradiction
           | cons hb tb => rw [bump_ht, bump_ht]; cases Hle with
             | step Hhead Htail => constructor; apply add_le_add_left; assumption; apply (t_ih tb n).mpr; assumption

def back (a : List F) : F :=
  helper a 0
where
  helper a r :=
    match a with
    | nil => r
    | cons h t => helper t h

theorem back_nil: back ([] : List F) = 0 := rfl 
theorem back_consnil: forall (h : F), back [h] = h := by intros; rfl
theorem back_conscons: forall {h1 h2 : F} {t}, back (h1::h2::t) = back (h2::t) := by intros; simp [back, back.helper]

theorem back_tail: forall t (h : F), t ≠ [] -> back (h::t) = back t := by
  intro t h H; cases t with
  | nil => contradiction
  | cons ht tt => rw [back_conscons]

theorem back_bump: forall {b : List F} {n}, b ≠ [] → back (bump b n) = n + back b := by
  intro b; induction b with
  | nil => intros; contradiction
  | cons hb tb tb_ih => intro n Hnil; cases tb with
    | nil => simp [back, back.helper, bump]
    | cons hb2 tb2 => simp [bump_ht,back_conscons]; apply tb_ih; intro Hfalse; cases Hfalse

-- XX move to Helper
theorem append_to_nil_left: forall {a b : List α}, a ++ b = [] -> a = [] := by
  intro a b Hab; cases a with
  | nil => trivial
  | cons h t => simp at Hab
theorem append_to_nil_right: forall {a b : List α}, a ++ b = [] -> b = [] := by
  intro a b Hab; rw [append_to_nil_left Hab] at Hab; simp at Hab; assumption

theorem back_app: forall {a b : List F}, b ≠ [] -> back (a ++ b) = back b := by
  intro a; induction a with
  | nil => simp
  | cons ha ta ta_ih => intro b Hb; simp; generalize Ht: ta ++ b = t; cases t with
    | nil => rw [append_to_nil_right Ht] at Hb; contradiction
    | cons hb tb => rw [back_conscons, <-Ht]; apply ta_ih; assumption

def join (a b : List F) : List F := a ++ (bump b (back a))

@[simp]
theorem join_nil_right: forall (a : List F), join a [] = a := by
  intro a; simp [join]; rw [bump_nil, append_nil]

@[simp]
theorem join_nil_left: forall (a : List F), join [] a = a := by
  intro a; simp [join, back, back.helper, bump_by_0]

theorem join_conscons: forall (a b : List F) h1 h2, join (h1::h2::a) b = h1::(join (h2::a) b) := by
  intro a b h1 h2; simp [join]; rw [back_conscons]

theorem join_head: forall {a b : List F} {h}, a ≠ [] → join (h::a) b = h::(join a b) := by
  intro a b h H; cases a with
  | nil => contradiction
  | cons h2 t => rw [join_conscons]

theorem join_nonempty_left: forall {a b : List F}, a ≠ [] -> join a b ≠ [] := by
  intro a b H; cases a with
  | nil => contradiction
  | cons h t => simp [join]

def Create (l : List (Nat × F)) : List F :=
    helper [] l
  where
    helper (sofar : List F) (l) : List F :=
      match l with
      | nil => sofar
      | cons h t => helper (join sofar (line h.1 h.2)) t
    line (size : Nat) (rate : F) : List F :=
      rep [] rate 0 size
    rep (rev : List F) (rate last : F) (left : Nat) : List F :=
      match left with
      | 0 => rev.reverse
      | left' + 1 => rep ((last + rate)::rev) rate (last + rate) left'

theorem join_back_single: forall (a : List F) b, back (join a [b]) = (back a) + b := by
  intro a; induction a with
  | nil => intros; simp [back_consnil, back_nil]
  | cons ha ta ta_ih => intro b; cases ta with
    | nil => simp [join, bump_ht, bump_nil, back_consnil, back_conscons]
    | cons ha2 ta2 => rw [join_conscons, back_conscons]; rw [back_tail]; apply ta_ih; simp [join]

theorem back_join_conscons: forall (h1 h2 : F) (t b), back (join (h1::h2::t) b) = back (join (h2::t) b) := by
  intros; simp [join, back_conscons]

theorem join_back: forall (a b : List F), back (join a b) = (back a) + (back b) := by
  intro a b
  have Ha: (Decidable (a = [])); exact List.hasDecEq a []
  cases Ha with
  | isTrue Hat => rw [Hat, join_nil_left, back_nil]; simp
  | isFalse Haf => 
     have Hb: (Decidable (b = [])); exact List.hasDecEq b []
     cases Hb with
     | isTrue Hbt => rw [Hbt, join_nil_right, back_nil]; simp
     | isFalse Hbf => revert b; revert a; intro a; induction a with
       | nil => intros; contradiction
       | cons ha ta ta_ih => intros Ha b Hb; cases ta with
         | nil => simp [join, back_consnil]; rw [back_tail]; apply back_bump; assumption; 
                  intro Hnil; apply bump_to_nil at Hnil; contradiction
         | cons hta tta => rw [back_conscons, back_join_conscons]; apply ta_ih; intro Hf; contradiction; assumption

/-
theorem Create_cons: forall (a : (Nat × F)) b, Create (a::b) = join (Create.line a.1 a.2) (Create b) := by
  intro a b; revert a; induction b with
  | nil => intro a; cases a; simp [Create, Create.helper, Create.line, Create.rep]
  | cons bh bt bt_ih => intro a; simp [Create, Create.helper]

theorem Create_app: forall (a b : List (Nat × F)), Create (a ++ b) = join (Create a) (Create b) := by
  intro a; induction a with
  | nil => intro b; simp [Create, Create.helper, join, join.helper, bump_by_0]
  | cons ha ta ta_ih => intro b; simp [Create, Create.helper, join, join.helper, bump_by_0]
-/
end specific
end Diagram
