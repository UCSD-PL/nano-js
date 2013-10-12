These are examples from the DRYAD suite:

   http://www.cs.uiuc.edu/~madhu/dryad/sl/examples/

(ported to JS)

Must 
----

  + singly-linked-list

  + doubly-linked-list

  + cyclic-list
    * dryad invariants are useless
    * express measures over binary args? (yes -- use the type)
          IF   the type of x is : dll(A,<y>)
          THEN should be able to use <y> in the measure definition... hmm.
 
  + sorted-list (only `rec` benchmarks, others need **axioms**)
    * insert_rec
    * insert_sort_rec 
    * merge_sort_rec  (NOT IN DRYAD)
    * quick_sort_rec  (NOT IN DRYAD) 

  + bst 
  - max-heap   <---- HEREHEREHEREHERE
  - avl-tree
  - tree-traversals

May
---

  - treap
  - rb-tree

Might
-----

  - binomial-heap
  - glib_gslist
  - glib_glist

