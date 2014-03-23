/*@ measure len  :: forall A. (dlist[A]) => number                      */
/*@ measure keys :: forall A. (dlist[A]) => set[number]                      */

/*@ measure dlenp :: forall A B C. (<l>+null, dlist[A,B,C]) => number   */
/*@ measure dlenp(p,x) = (if (p = null) then 0 else len(x))             */

/*@ measure dkeysp :: forall A B C. (<l>+null, dlist[A,B,C]) => set[number]  */
/*@ measure dkeysp(p,x) = (if (p = null) then
                            Set_cap(Set_sng(1),Set_sng(0))
                         else
                            keys(x))                                    */

/*@
  type dlist[A,S,P] exists! l |-> tl:dlist[A, <l>, S]
                                . me:{ data: A, next:<l>+null, prev:P }
    with len(x) = (1 + dlenp(field(me, "next"), tl))
    and keys(x) = Set_cup(Set_sng(field(me, "data")), dkeysp(field(me, "next"), tl))

*/
