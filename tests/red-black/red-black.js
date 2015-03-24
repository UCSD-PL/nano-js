/*@ measure col    :: forall A. (rbtree[A]) => number           */
/*@ measure bheight :: forall A. (rbtree[A]) => number */
/*@ measure keys  :: forall A. (rbtree[A]) => set[number] */

/*@ type rbtree [A] < p :: (A,A) => prop, q :: (A,A) => prop >
      exists! l |-> lt:{v:rbtree[A<p key>]<p,q> | bheight(v) = bheight(rt)}
            * r |-> rt:{v:rbtree[A<q key>]<p,q> | bheight(v) = bheight(lt)}.
        root: { color : { v:number | ((v != 0) => ((col(rt)  = 0) && ((col(lt)  = 0)))) }
              , key   : A
              , left  : <l>+null
              , right : <r>+null
              }

      col(null) = 0        
      col(x)    =  field_int(root, "color")
      
      keys(null) = (Set_cap(Set_sng(0),Set_sng(1)))
      keys(x)    = (keys(lt) ∪ keys(rt) ∪1 field_int(root, "key"))

      bheight(null) = 1
      bheight(x)    = ((if (field_int(root,"color") = 0) then 1 else 0) + bheight(lt))
*/
 

/*@ invariant {v:rbtree[number] | ((bheight(v) > 0) && ((Prop(nil(v)) => (col(v) = 0)))
                                                     && ((Prop(nil(v)) => (bheight(v) = 1)))
                                                     && ((Prop(nil(v)) => (keys(v) = Set_cap(Set_sng(0),Set_sng(1))))))} */
