/*@ measure len  :: forall A. (list[A]) => number  */
/* measure lenp :: forall A. (<l> + null, list[A]) => number */
/* measure lenp(p,x) = (if (p = null) then 0 else len(x)) */

/*@ measure keys ::  forall A. (list[A]) => set[number]  */
/* measure keysp :: forall A. (<l> + null, list[A]) => set[number]  */
/* measure keysp(p,x) = (if (p = null) then Set_cap(Set_sng(1),Set_sng(0)) else
   keys(x)) */

/*@
type list[A] exists! l |-> tl:list[A] .
                    r:{ data : A, next : {v:<l> + null | (Prop(nil(v)) <=> Prop(nil(tl)))} }

    with len(x) = (if Prop(nil(x)) then 0 else 1 + len(tl))
    and keys(x) = (if Prop(nil(x)) then Set_cap(Set_sng(1),Set_sng(0)) 
                                   else Set_cup(Set_sng(field_int(r, "data")), keys(tl)))
*/

/*@ invariant {v:list[number] | ((len(v) >= 0) && ((Prop(nil(v)) => (len(v) = 0)))
                                               && ((Prop(nil(v)) => (keys(v) = Set_cap(Set_sng(0),Set_sng(1))))))} */
/*@ qualif Q1(v:T,x:T,y:T): (len(v) = len(x) + len(y)) */
/*@ qualif Q2(v:T,x:T,y:T): (keys(v) = Set_cup(keys(x),keys(y))) */
