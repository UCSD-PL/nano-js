/*@ qualif PApp(v:a) : papp1(p, v) */

/*@ measure setok :: forall A. set[A] */

/*@ measure keys  :: forall A. (list[A]) => set[number]  */
/*@ measure keysp :: forall A. (<l> + null, list[A]) => set[number]  */
/*@ measure keysp(p,x) = (if (p != null) then keys(x) else (Set_cap(Set_sng(0),Set_sng(1)))) */

/*@ measure len  :: forall A. (list[A]) => number  */
/*@ measure lenp :: forall A. (<l> + null, list[A]) => number */
/*@ measure lenp(p,x) = (if (p = null) then 0 else len(x)) */

/* measure hd :: forall A. (list[A]) => A */

/* ---------------- -------------- ---------------- */
/* ---------------- ---- LISTS --- ---------------- */
/* ---------------- -------------- ---------------- */

/*@
type list[A]<p :: (A, A) => prop>
        exists! l |-> tl:list[A<p (field t "data")>]<p>. 
          t:{ data : A, next : <l> + null }

     with len(x)   = 1 + lenp(field(t, "next"), tl)
     and keys(x)   = Set_cup(Set_sng(field(t, "data")), keysp(field(t, "next"), tl))
*/
