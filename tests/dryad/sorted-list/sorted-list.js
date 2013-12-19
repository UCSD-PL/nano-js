/*@ measure keys :: forall A. (list[A]+incList[A]) => set[A]  */
/*@ measure keysp :: forall A. (<l> + null, list[A]+incList[A]) => set[A]  */
/*@ measure keysp(p,x) = (if (p = null) then Set_cap(Set_sng(1),Set_sng(0)) else
   keys(x)) */

/*@ measure len  :: forall A. (list[A]+incList[A]) => number  */
/*@ measure lenp :: forall A. (<l> + null, list[A]+incList[A]) => number */
/*@ measure lenp(p,x) = (if (p = null) then 0 else len(x)) */

/* ---------------- -------------- ---------------- */
/* ---------------- SORTED   LISTS ---------------- */
/* ---------------- -------------- ---------------- */

/*@ type incList[A]
      exists! l |-> tl:incList[{v:A | field(hd, "data") <= v }]
      . hd:{ data : A, next : <l> + null }

      with len(x)  = 1 + lenp(field(hd, "next"), tl)
      and  keys(x) = Set_cup(Set_sng(field(hd, "data")),
                                     keysp(field(hd, "next"),tl))
*/

/* ---------------- -------------- ---------------- */
/* ---------------- UNSORTED LISTS ---------------- */
/* ---------------- -------------- ---------------- */

/*@
type list[A] exists! l |-> tl:list[A] . r:{ data : A, next : <l> + null }

     with len(x) = 1 + lenp(field(r, "next"), tl)
     and keys(x) = Set_cup(Set_sng(field(r, "data")), keysp(field(r, "next"), tl))
*/
