theory BPlusTree_ImpRange
imports
  BPlusTree_Range
  BPlusTree_Iter
begin

(* Adding an actual range iterator based on the normal iterator
is trivial (just forward until we reach the first element \<ge> and stop
as soon as we have an element <)
We *could* implement a search for the first element of the range
however cannot make any (simple) guarantees on its quality
(see Bplustree_Range to see why *)


end