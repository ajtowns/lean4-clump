/- Deal with gathering txs into chunks -/

import Init.Data.List.Basic
import Lean.Data.Rat           -- rational numbers
import Mathlib.Data.List.Perm  -- (l1 ~ l2) is true if list l2 is a permutation of list l1
import Std.Data.Rat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Order
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.ByContra

import Clump.Helper
import Clump.Basic
import Clump.Feerate
import Clump.Diagram

universe u

open List
open Rat

namespace CluMP

section specific
set_option quotPrecheck.allowSectionVars true

open Cluster
open Diagram

variable {Tx : Type u} [DecidableEq Tx] [Cluster Tx]

theorem singleton_nonempty (t : Tx): [t] ≠ [] := by simp

def Raise (l : List Tx) : Chunking Tx := map (fun el => ⟨[el], singleton_nonempty el⟩) l
def Drop (c : Chunking Tx) : List Tx := (map (fun el => el.val) c).join

theorem app_raise: forall (a b : List Tx), Raise (a ++ b) = (Raise a) ++ (Raise b) := by
  intro a; induction a with
  | nil => simp [Raise]
  | cons h t t_ih => intro b; simp [Raise, t_ih]

theorem app_drop: forall (a b : Chunking Tx), Drop (a ++ b) = (Drop a) ++ (Drop b) := by
  intro a; induction a with
  | nil => simp [Drop]
  | cons h t t_ih => intro b; simp [Drop, t_ih]

theorem append_vs_cons {a : α} {b : List α} : a::b = [a] ++ b := by simp

theorem drop_raise: forall (a : List Tx), Drop (Raise a) = a := by
  intro a; induction a with
  | nil => simp [Raise, Drop]
  | cons h a2 a2_ih => rw [append_vs_cons, app_raise, app_drop, a2_ih]; rfl

def ToDiagram (l : Chunking Tx) : List Rat :=
  Diagram.Create (map (fun c => (c.Size, c.Fee/.c.Size)) l)

/-- Provides ≤ notation for diagram comparison -/
instance : LE (Chunking Tx) where
  le (a b : Chunking Tx) := (ToDiagram a) ≤ (ToDiagram b)

instance dec_Chunking_le : forall (x y : Chunking Tx), Decidable (x ≤ y) := by
  intro x y; simp [LE.le]; apply Diagram.decLE

/-- Chunk merges -/
inductive GenMerge : Chunking Tx -> Chunking Tx -> Prop where
  | done : GenMerge [] []
  | skip (h t1 t2) : GenMerge t1 t2 -> GenMerge (h::t1) (h::t2)
  | merge (h1 h2 t1 t2) : (h1 < h2) -> GenMerge t1 t2 -> GenMerge (h1::h2::t1) ((h1 ++ h2)::t2)

theorem GenMerge.rfl : forall (a : Chunking Tx), GenMerge a a := by
  intro a; induction a with
  | nil => apply GenMerge.done
  | cons h t t_ih => apply GenMerge.skip; assumption

theorem GenMerge.improve : forall (a b : Chunking Tx), GenMerge a b -> a <= b := by
  intro a b GM; induction GM with
  | done => simp [LE.le, ToDiagram]; constructor
  | skip => simp [LE.le, ToDiagram]; sorry
  | merge => sorry

theorem GenMerge.antisym : forall (a b : Chunking Tx), GenMerge a b -> b <= a -> a = b := sorry

def Merge.back (next : Chunk Tx) (back : (Chunking Tx)) :=
  match back with
   | [] => [next]
   | check::back' => if (check < next) then (Merge.back (check ++ next) back') else next::check::back'

def Merge.helper (fin todo : Chunking Tx) :=
  match todo with
  | [] => fin.reverse
  | chunk::todo' => Merge.helper (Merge.back chunk fin) todo'

/-- Implements merging in linear time -/
def Merge (c : Chunking Tx) : Chunking Tx :=
  Merge.helper [] c

theorem cons_as_append: forall (l : List α) (h), h::l = [h] ++ l := by intro l h; rfl

theorem Merge_repeat_nop: forall (a : Chunking Tx), Merge a = Merge (Merge a) := sorry
    

theorem Merge_app_left: forall (a b : Chunking Tx), Merge (a ++ b) = Merge ((Merge a) ++ b) := by
  intro a; induction a with
  | nil => simp; sorry
  | cons h t t_ih => sorry

theorem Merge_app_right: forall (a b : Chunking Tx), Merge (a ++ b) = Merge (a ++ (Merge b)) := sorry
theorem Merge_app_both: forall (a b : Chunking Tx), Merge (a ++ b) = Merge ((Merge a) ++ (Merge b)) := sorry


theorem Merge_Raise_Drop: forall (a : Chunking Tx), Drop (Merge a) = Drop a := by sorry

theorem Merge_gt: forall (a : Chunking Tx), Merge a >= a := sorry
theorem Merge_best: forall (a : Chunking Tx), Merge (Raise $ Drop a) >= Merge a := sorry
/-
theorem Merge_app_iff: forall (a b : List Tx), Merge [a, b] = [a ++ b] ↔ (a < b) := by
  intro a b; constructor
  . intros Hmerge; simp [Merge, Merge.helper, Merge.back] at Hmerge; rw [chunk_lt_rat_lt]; by_contra H; simp [H] at Hmerge
  . intros Hlt; simp [Merge, Merge.helper, Merge.back]; rw [chunk_lt_rat_lt] at Hlt; simp [Hlt]
  
theorem Merge_app_cmp_left: forall (a b : List Tx), Merge [a, b] = [a ++ b] -> a < (a ++ b) := by sorry
theorem Merge_app_cmp_right: forall (a b : List Tx), Merge [a, b] = [a ++ b] -> (a ++ b) < b := by sorry

/-- If the start of a chunk gets merged with an earlier block, the rest of the chunk also gets merged -/
theorem Merge_tail: forall (a b : List Tx), Merge (Raise (a ++ b)) = [a ++ b] → forall (c), Merge (Raise (c ++ a)) = [c ++ a] -> Merge (Raise (c ++ a ++ b)) = [c ++ a ++ b] := by
  intro a b Hab c Hca
  rw [append_assoc,app_raise]
-/

end specific
end CluMP
