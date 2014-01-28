/*@ qualif PApp(v:a) : papp1(p, v) */

/*@ measure keys :: (list[number]) => set[number]  */
/*@ measure keysp ::(<l> + null, list[number]) => set[number]  */
/*@ measure keysp(p,x) = (if (p = null) then Set_cap(Set_sng(0), Set_sng(1)) else keys(x)) */

/*@ measure len  :: (list[number]) => number  */
/*@ measure lenp :: (<l> + null, list[number]) => number */
/*@ measure lenp(p,x) = (if (p = null) then 0 else len(x)) */

/*@ measure hd :: (list[A]) => A */

/* ---------------- -------------- ---------------- */
/* ---------------- ---- LISTS --- ---------------- */
/* ---------------- -------------- ---------------- */

/*@
type list[A]<p :: (A, A) => prop>
        exists! l |-> tl:list[A<p (field t "data")>]<p>. 
          t:{ data : A, next : <l> + null }

     with len(x)   = 1 + lenp(field(t, "next"), tl)
     and keys(x)   = Set_cup(Set_sng(field(t, "data")), keysp(field(t, "next"), tl))
     and   hd(x)   = field(t, "next")
*/
