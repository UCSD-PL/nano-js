/*@ measure keys :: forall A. (tree[A]) => set[number]  */
/*@ measure keysp :: forall A. (<l> + null, tree[A]) => set[number]  */
/*@ measure keysp(p,x) = (if (p = null) then Set_cap(Set_sng(1),Set_sng(0)) else keys(x)) */

/*@
  type tree[A] <p :: (A, A) => prop, q :: (A, A) => prop>
       exists! l |-> lh:tree[A<p (field_int me "key")>]<p, q>
             * r |-> rh:tree[A<q (field_int me "key")>]<p, q>
               . me:{ left:<l>+null
                    , key:A
                    , right:<r>+null
                    }

     with  keys(x) = Set_cup(Set_sng(field_int(me, "key")),
                              Set_cup(keysp(field_Ref(me, "left"), lh),
                                      keysp(field_Ref(me, "right"), rh)))
*/
