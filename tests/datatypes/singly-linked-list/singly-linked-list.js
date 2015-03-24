/*@ measure len  :: forall A. (list[A]) => number  */
/*@ measure keys ::  forall A. (list[A]) => set[number]  */

/*@
type list[A] exists! l |-> tl:list[A] .
                    r:{ data : A, next : <l> + null }

     len(null) = 0
     len(x)    = 1 + len(tl)

     keys(null) = Set_cap(Set_sng(1),Set_sng(0))
     keys(x)    = Set_cup(Set_sng(field_int(r, "data")), keys(tl))

*/

/*@ invariant {v:list[number] | (len(v) >= 0) } */

/*@ qualif Q1(v:T,x:T,y:T): (len(v) = len(x) + len(y)) */
/*@ qualif Q2(v:T,x:T,y:T): (keys(v) = Set_cup(keys(x),keys(y))) */
