import Clump.Basic

open AJHelper
open List
open CluMP

-- For messing about with #eval, we'll allow writing a tx as (fee, size)
@[default_instance]
instance : HCluster (Int × Nat) where
  parent := fun _ _ => False
  parent_sensible := by intros; contradiction
  Fee tx := if let Nat.succ _ := tx.2 then tx.1 else 0
  Size tx := tx.2
  zerosize_zerofee := by simp

def a : (List (List (Int × Nat))) := [[(1,4),(2,3)],[(2,4)]]
def b : (List (List (Int × Nat))) := [[(3,7)],[(1,2),(1,2)]]

#eval Diagram [[(1,4),(2,3)],[(2,4)]]
#eval (a ≤d b)
#eval (a ≥d b)
