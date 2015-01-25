/*@ measure col    :: forall A. (rbtree[A]) => number           */
/*@ measure bheight :: forall A. (rbtree[A]) => number */
/*@ measure keys  :: forall A. (rbtree[A]) => set[number] */

/*@ type rbtree [A] < p :: (A,A) => prop, q :: (A,A) => prop >
      exists! l |-> lt:{v:rbtree[A<p key>]<p,q> | bheight(v) = bheight(rt)}
            * r |-> rt:{v:rbtree[A<q key>]<p,q> | bheight(v) = bheight(lt)}.
        root: { color : { v:number | ((v != 0) => ((col(rt)  = 0) && ((col(lt)  = 0)))) }
              , key   : A
              , left  : {v:<l>+null | (Prop(nil(v)) <=> Prop(nil(lt))) }
              , right : {v:<r>+null | (Prop(nil(v)) <=> Prop(nil(rt))) }
              }

              
      with col(x)   = (if (Prop(nil(x))) then 0 else field_int(root, "color"))
      
      and  keys(x)    = (if (Prop(nil(x))) then (Set_cap(Set_sng(0),Set_sng(1))) else (keys(lt) ∪ keys(rt) ∪1 field_int(root, "key")))

      and  bheight(x) = (if (Prop(nil(x))) then 1 else (if (field_int(root,"color") = 0) then 1 else 0) + bheight(lt))
*/
 

/*@ invariant {v:rbtree[number] | ((bheight(v) > 0) && ((Prop(nil(v)) => (col(v) = 0)))
                                                     && ((Prop(nil(v)) => (bheight(v) = 1)))
                                                     && ((Prop(nil(v)) => (keys(v) = Set_cap(Set_sng(0),Set_sng(1))))))} */
