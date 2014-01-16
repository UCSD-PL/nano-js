/*@ qualif PApp(v:a) : papp1(p, v) */

/*@ measure keys :: (list[number]+incList[number]) => set[number]  */
/*@ measure keysp ::(<l> + null, list[number]+incList[number]) => set[number]  */
/*@ measure keysp(p,x) = (if (p = null) then Set_cap(Set_sng(0), Set_sng(1)) else keys(x)) */

/*@ measure len  :: (list[number]+incList[number]) => number  */
/*@ measure lenp :: (<l> + null, list[number]+incList[number]) => number */
/*@ measure lenp(p,x) = (if (p = null) then 0 else len(x)) */
/* ---------------- -------------- ---------------- */
/* ---------------- ---- LISTS --- ---------------- */
/* ---------------- -------------- ---------------- */

/*@
type list[A]<p :: (A, A) => prop>
        exists! l |-> tl:list[A<p (field hd "data")>]<p>. 
          hd:{ data : A, next : <l> + null }

     with len(x)   = 1 + lenp(field(hd, "next"), tl)
     and keys(x)   = Set_cup(Set_sng(field(hd, "data")), keysp(field(hd, "next"), tl))
*/
