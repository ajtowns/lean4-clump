/- Basics of the cluster mempool data structure -/

import Init.Data.List.Basic
import Std.Data.Rat.Basic
import Clump.Basic

universe u

open List
open Rat

namespace CluMP

-- This is the data we're working on
class Cluster (Tx : Type u) where
  parent : Tx -> Tx -> Prop
  parent_sensible : ∀ (p c : Tx), parent p c -> ¬ (RTC parent p c)
  Fee : Tx -> Int
  Size : Tx -> Nat
  zerosize_zerofee : ∀ (t : Tx), Size t = 0 -> Fee t = 0

/--
 Theory is:
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

end CluMP
