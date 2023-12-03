/- Basics of the cluster mempool data structure -/

import Init.Data.List.Basic
import Clump.Helper

universe u

open List

namespace CluMP

-- This is the data we're working on
class Cluster (Tx : Type u) [DecidableEq Tx] where
  parent : Tx -> Tx -> Prop
  decParent : ∀ (a b : Tx), Decidable (parent a b)
  parent_sensible : ∀ (p c : Tx), parent p c -> ¬ (RTC parent p c)
  Fee : Tx -> Int
  Size : Tx -> Nat
  zerosize_zerofee : ∀ (t : Tx), Size t = 0 -> Fee t = 0

/-- Chunks are non-empty lists of txs -/
def Chunk (Tx : Type u) [DecidableEq Tx] := { l : List Tx // l ≠ [] }

/-- Chunkings are a list of chunks -/
abbrev Chunking (Tx : Type u) [DecidableEq Tx] := List (Chunk Tx)

/--
 Theory is:
    Reorder (c : Chunk) (other : List Tx) : Chunk -- reorder "chunk" to be in "other" order??

    theorems:
      Perm (Reorder a o) a -- Reordering just reorders

      -- if a particular set of txs is the first chunk, optimising just those txs generates the same chunk
      Merge a = h::t -> Merge [Raise h] = [h]

      -- reordering a chunk only improves things
      Merge a = [[Drop a]] -> Perm (Drop a) (Drop b) -> Merge b >= Merge (Raise a)

    pim-first base cmp:
      Reorder (head (Merge (Raise base))) cmp



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
