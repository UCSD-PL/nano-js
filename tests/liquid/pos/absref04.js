/*@
type list[A]<p :: (A, A) => prop>
        exists! l |-> tl:list[A<p data>]<p>. 
          r:{ data : A, next : <l> + null }
     with len(x) = 1 + lenp(field_ref(r, "next"), tl)
*/
     //and keys(x) = Set_sng(field_A(r, "data")) ∪ keysp(field_ref(r, "next"), tl)

/*@ measure len  :: forall A. (list[A]) => number  */
/*@ measure lenp :: forall A. (<l> + null, list[A]) => number */
/*@ measure lenp(p,x) = (if (p = null) then 0 else len(x)) */

/* measure keys  :: (list[number])             => set[number]  */
/* measure keysp :: (<l> + null, list[number]) => set[number]  */
/* measure keysp(p,x) = (if (p = null) then (Set_sng(0) ∩ Set_sng(1)) else keys(x)) */

/* qualif LtField(v:a, x:a): v < field_A(x, "data") */
/* qualif LtField(v:a, x:a): v <= field_A(x, "data") */
/* qualif LtField(v:a, x:a): v = field_A(x, "data") */
/* qualif LtField(v:a, x:a): v >= field_A(x, "data") */
/* qualif LtField(v:a, x:a): v > field_A(x, "data") */

/*@ consSorted :: forall A.
  (p:<p>, k:A)/p |-> ps:list[{v:A | v > k}]<{\h v -> h <= v}>
   => {v:<l> | true} /l |-> ls:list[A]<{\h v -> h <= v}>*/
function consSorted(p,k) {
  var y = {};
  y.data = k;
  y.next = p;
  return y;
}
