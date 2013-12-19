/*@ measure hd :: forall A. (tree[A]) => A                               */

/*@ measure keys :: forall A. (tree[A]) => set[A]  */
/*@ measure keysp :: forall A. (<l> + null, tree[A]) => set[A]  */
/*@ measure keysp(p,x) = (if (p = null) then Set_cap(Set_sng(1),Set_sng(0)) else keys(x)) */

/*@ type tree[A] exists! l |-> sls:tree[{A | v < field(me, "data")}]
                       * r |-> srs:tree[{A | v > field(me, "data")}]
                       . me:{ data: A, left:<l>+null, right:<r>+null } 

       with hd(x)    = field(me, "data")

       and  keys(x) = Set_cup(Set_sng(field(me, "data")),
                              Set_cup(keysp(field(me, "left"), sls),
                                      keysp(field(me, "right"), srs)))
 */

