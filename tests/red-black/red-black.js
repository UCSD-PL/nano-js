/*@ measure color    :: forall A. (rbtree[A]) => number                        */
/*@ measure colorp   :: forall A. (<l>+null,rbtree[A]) => number               */
/*@ measure colorp(p,x) = (if (p = null) then 0 else color(x))     */

/*@ measure bheight  :: forall A. (rbtree[A]) => number                        */
/*@ measure bheightp :: forall A. (<l>+null,rbtree[A]) => number               */
/*@ measure bheightp(p,x) = (if (p = null) then 1 else bheight(x)) */

/*@ measure keys  :: forall A. (rbtree[A]) => set[number] */
/*@ measure keysp :: forall A. (<l>+null, rbtree[A]) => set[number] */
/*@ measure keysp(p,x) = (if p = null then (Set_sng(0) ∩ Set_sng(1)) else keys(x)) */

/* measure preKey :: forall A. (rbtree[A]) => number */
/* measure postKey :: forall A. (rbtree[A]) => number */

/*@ type rbtree [A] < p :: (A,A) => prop, q :: (A,A) => prop >
      exists! l |-> lt:rbtree[A<p key>]<p,q>
            * r |-> rt:rbtree[A<q key>]<p,q>.
        root: { color : { v:number | ((v != 0) => 
                                         ((colorp(field_Ref(root,"right"),rt)  = 0) &&
                                         ((colorp(field_Ref(root,"left"),lt)   = 0)))) }
              , key   : A
              , left  : {v:<l>+null | (bheightp(v,lt) = bheightp(field_Ref(root,"right"),rt))}
              , right : {v:<r>+null | (bheightp(v,rt) = bheightp(field_Ref(root,"left"),lt))}
              }                                              
              
      with color(x)   = field_int(root, "color")
      
      and  keys(x)    = keysp(field_Ref(root,"left"),lt) ∪ keysp(field_Ref(root,"right"),rt) ∪1 field_int(root, "key")

      and  bheight(x) = ((if (field_int(root,"color") = 0) then 1 else 0)
                        +(if (bheightp(field_Ref(root,"left"), lt)
                               <= bheightp(field_Ref(root,"right"), rt)) then
                            bheightp(field_Ref(root,"right"),rt)
                          else
                            bheightp(field_Ref(root,"left"),lt)))
*/
 
