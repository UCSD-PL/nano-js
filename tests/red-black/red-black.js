/*@ measure color    :: forall A. (rbtree[A]) => number                        */
/*@ measure colorp   :: forall A. (<l>+null,rbtree[A]) => number               */
/*@ measure colorp(p,x) = (if (p = null) then 0 else color(x))     */

/*@ measure bheight  :: forall A. (rbtree[A]) => number                        */
/*@ measure bheightp :: forall A. (<l>+null,rbtree[A]) => number               */
/*@ measure bheightp(p,x) = (if (p = null) then 1 else bheight(x)) */

/*@ measure keys  :: forall A. (rbtree[A]) => set[number] */
/*@ measure keysp :: forall A. (<l>+null, rbtree[A]) => set[number] */
/*@ measure keysp(p,x) = (if p = null then Set_sng(0) ∩ Set_sng(1) else keys(x)) */

/*@ measure preKey :: forall A. (rbtree[A]) => number */
/*@ measure postKey :: forall A. (rbtree[A]) => number */

/*@ type rbtree [A] < p :: (A,A) => prop, q :: (A,A) => prop >
      exists! l |-> lt:rbtree[A<p key>]<p,q>
            * r |-> rt:rbtree[A<q key>]<p,q>.
        root: { color : { v:number | ((v != 0) => 
                                         ((colorp(field(root,"right"),rt)  = 0) &&
                                         ((colorp(field(root,"left"),lt)   = 0)))) }
              , key   : A
              , left  : {v:<l>+null | (bheightp(v,lt) = bheightp(field(root,"right"),rt))}
              , right : {v:<r>+null | (bheightp(v,rt) = bheightp(field(root,"left"),lt))}
              }                                              
              
      with color(x)   = field(root, "color")
      
      and preKey(x)   = (if (field(root,"left") != null) then preKey(lt) else field(root,"key"))
      and postKey(x)  = (if (field(root,"right") != null) then postKey(rt) else field(root,"key"))
      
      and  keys(x)    = keys(lt) ∪ keys(rt) ∪1 field(root, "key")

      and  bheight(x) = ((if (field(root,"color") = 0) then 1 else 0)
                        +(if (bheightp(field(root,"left"), lt)
                               <= bheightp(field(root,"right"), rt)) then
                            bheightp(field(root,"right"),rt)
                          else
                            bheightp(field(root,"left"),lt)))
*/
 
