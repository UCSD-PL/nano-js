/*@ measure len  :: forall A. (dlist[A]) => number                      */
/*@ measure keys :: (dlist[number]) => set[number]                      */

/*@
  type dlist[A,S,P]
    exists! l |-> tl:dlist[A, <l>, S].
            me:{ data: A, next:{v:<l>+null | (Prop(nil(v)) => Prop(nil(tl)))}, prev:P }
                                
    len(null) = 0                               
    len(x)    = (1 + len(tl))
    
    keys(null) = Set_cap(Set_sng(0),Set_sng(1))
    keys(x)    = Set_cup(Set_sng(field_int(me, "data")), keys(tl))
*/

/*@ invariant {v:dlist[number,<l>,<m>] | ((len(v) >= 0) 
                                      && ((Prop(nil(v)) => (len(v) = 0)))
                                      && ((Prop(nil(v)) => (keys(v) = Set_cap(Set_sng(0),Set_sng(1))))))} */
