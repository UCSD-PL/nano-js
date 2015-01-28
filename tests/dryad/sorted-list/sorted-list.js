/*@ qualif PApp(v:a) : papp1(p, v) */

/* measure setok :: forall A. set[A] */

/*@ measure keys  :: forall A. (list[A]) => set[number]  */
/* measure keysp :: forall A. (<l> + null, list[A]) => set[number]  */
/* measure keysp(p,x) = (if (p != null) then keys(x) else (Set_cap(Set_sng(0),Set_sng(1)))) */

/*@ measure len  :: forall A. (list[A]) => number  */
/* measure lenp :: forall A. (<l> + null, list[A]) => number */
/* measure lenp(p,x) = (if (p = null) then 0 else len(x)) */

/* ---------------- -------------- ---------------- */
/* ---------------- ---- LISTS --- ---------------- */
/* ---------------- -------------- ---------------- */

/* type incList[A] = list[A]<\h v -> h <= v>

/*@
type list[A]<p :: (A, A) => prop>
        exists! l |-> tl:list[A<p data>]<p>. 
          r:{ data : A, next : <l> + null }

    with len(x) = (if Prop(nil(x)) then 0 else 1 + len(tl))
    and keys(x) = (if Prop(nil(x)) then Set_cap(Set_sng(1),Set_sng(0)) 
                                   else Set_cup(Set_sng(field_int(r, "data")), keys(tl)))
*/

/*@ invariant {v:list[A] | ((len(v) >= 0) && ((Prop(nil(v)) => (len(v) = 0)))
                                          && ((Prop(nil(v)) => (keys(v) = Set_cap(Set_sng(0),Set_sng(1))))))} */

/*@ qualif LenInc(v:T, x:T): (len(v) = 1 + len(x)) */
/*@ qualif KeysInc(v:T, x:T, y:a): (keys(v) = Set_cup(Set_sng(y),keys(x))) */
/*@ qualif Len1(v:T,x:T,y:T): (len(v) = len(x) + len(y)) */
/*@ qualif Len2(v:T,x:T,y:T): (len(x) = len(v) + len(y)) */
/*@ qualif Keys1(v:T,x:T,y:T): (keys(v) = Set_cup(keys(x),keys(y))) */
/*@ qualif Keys2(v:T,x:T,y:T): (keys(x) = Set_cup(keys(v),keys(y))) */
