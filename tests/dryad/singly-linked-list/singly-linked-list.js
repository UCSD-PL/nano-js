/*@ measure len  :: forall A. (list[A]) => number  */
/*@ measure lenp :: forall A. (<l> + null, list[A]) => number */
/*@ measure lenp(p,x) = (if (p = null) then 0 else len(x)) */

/*@ measure keys ::  forall A. (list[A]) => set[number]  */
/*@ measure keysp :: forall A. (<l> + null, list[A]) => set[number]  */
/*@ measure keysp(p,x) = (if (p = null) then Set_cap(Set_sng(1),Set_sng(0)) else
   keys(x)) */

/*@
type list[A] exists! l |-> tl:list[A] . r:{ data : A, next : <l> + null }

     with len(x) = 1 + lenp(field_Ref(r, "next"), tl)
     and keys(x) = Set_cup(Set_sng(field_int(r, "data")), keysp(field_Ref(r, "next"), tl))

*/
