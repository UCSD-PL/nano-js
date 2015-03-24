/*@ measure keys  :: forall A. (list[A]) => set[number]  */

/*@ measure len  :: forall A. (list[A]) => number  */

/* ---------------- -------------- ---------------- */
/* ---------------- ---- LISTS --- ---------------- */
/* ---------------- -------------- ---------------- */

/* type incList[A] = list[A]<\h v -> h <= v>

/*@
type list[A]<p :: (A, A) => prop>
        exists! l |-> tl:list[A<p data>]<p>. 
          r:{ data : A, next : <l> + null }

    len(null)  = 0
    len(x)     = 1 + len(tl)
    
    keys(null) = Set_cap(Set_sng(0),Set_sng(1))
    keys(x)    = Set_cup(Set_sng(field_int(r,"data")),keys(tl))

*/

/*@ invariant {v:list[A] | ((len(v) >= 0) && ((Prop(nil(v)) => (len(v) = 0)))
                                          && ((Prop(nil(v)) => (keys(v) = Set_cap(Set_sng(0),Set_sng(1))))))} */

/*@ qualif Len1(v:T, x:T): (len(v) = len(x) + 1) */
/*@ qualif Keys1(v:T, x:T, k:a): (keys(v) = Set_cup(Set_sng(k), keys(x))) */
/*@ qualif Len1(v:T,x:T,y:T): (len(v) = len(x) + len(y)) */
/*@ qualif Len2(v:T,x:T,y:T): (len(x) = len(v) + len(y)) */
/*@ qualif Keys1(v:T,x:T,y:T): (keys(v) = Set_cup(keys(x),keys(y))) */
/*@ qualif Keys2(v:T,x:T,y:T): (keys(x) = Set_cup(keys(v),keys(y))) */
