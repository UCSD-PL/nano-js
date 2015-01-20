/*@ qualif PApp(v:a) : papp1(p, v) */

/* measure setok :: forall A. set[A] */

/*@ measure len  :: forall A. (list[A]) => number  */
/*@ measure lenp :: forall A. (<l> + null, list[A]) => number */
/*@ measure lenp(p,x) = (if (p = null) then 0 else len(x)) */

/* ---------------- -------------- ---------------- */
/* ---------------- ---- LISTS --- ---------------- */
/* ---------------- -------------- ---------------- */

/* type incList[A] = list[A]<\h v -> h <= v>

/*@
type list[A]
        exists! l |-> tl:list[A]. 
          me:{ data : A, next : <l> + null }

     with len(x)   = 1 + lenp(field_Ref(me, "next"), tl)
*/
