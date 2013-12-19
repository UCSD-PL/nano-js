/*@ measure hd :: forall A. (btree[A]+heap[A]) => A                               */

/*@ measure keys :: forall A. (btree[A]+heap[A]) => set[A]  */
/*@ measure keysp :: forall A. (<l> + null, btree[A]+heap[A]) => set[A]  */
/*@ measure keysp(p,x) = (if (p = null) then Set_cap(Set_sng(1),Set_sng(0)) else keys(x)) */

/*@
  type btree[A]
       exists! l |-> lh:btree[A] * r |-> rh:btree[A]
               . me:{ left:<l>+null
                    , key:A
                    , right:<r>+null
                    }

     with hd(x)   = field(me, "key")
     and  keys(x) = Set_cup(Set_sng(field(me, "key")),
                              Set_cup(keysp(field(me, "left"), lh),
                                      keysp(field(me, "right"), rh)))
*/
/*@
  type heap[A]
       exists! l |-> lh:heap[{A | (v <= field(me, "key"))}]
             * r |-> rh:heap[{A | (v <= field(me, "key"))}]
               . me:{ left:<l>+null
                    , key:A
                    , right:<r>+null
                    }

     with hd(x)   = field(me, "key")
     and  keys(x) = Set_cup(Set_sng(field(me, "key")),
                              Set_cup(keysp(field(me, "left"), lh),
                                      keysp(field(me, "right"), rh)))
*/
