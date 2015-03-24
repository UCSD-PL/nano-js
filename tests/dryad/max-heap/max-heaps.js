/*@ measure keys :: forall A. (tree[A]) => set[number]  */

/*@
  type tree[A] <p :: (A, A) => prop, q :: (A, A) => prop>
       exists! l |-> lh:tree[A<p (field_int me "key")>]<p, q>
             * r |-> rh:tree[A<q (field_int me "key")>]<p, q>
               . me:{ left:{v:<l>+null | ((Prop (nil v)) => (Prop (nil lh)))}
                    , key:A
                    , right:{v:<r>+null | ((Prop (nil v)) => (Prop (nil rh)))}
                    }
      keys(null) = Set_cap(Set_sng(1),Set_sng(0))
      keys(x)    = Set_cup(Set_cup(Set_sng(field_int(me, "key")),keys(lh)),keys(rh))
*/
