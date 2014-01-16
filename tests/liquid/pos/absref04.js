/*@
type list[A]<p :: (A, A) => prop>
        exists! l |-> tl:list[A<p (field r "data")>]<p>. 
          r:{ data : A, next : <l> + null }
     with len(x) = 1 + lenp(field(r, "next"), tl)
     and keys(x) = Set_sng(field(r, "data")) ∪ keysp(field(r, "next"), tl)

*/

/*@ measure len  :: (list[number]+incList[number]) => number  */
/*@ measure lenp :: (<l> + null, list[number]+incList[number]) => number */
/*@ measure lenp(p,x) = (if (p = null) then 0 else len(x)) */

/*@ measure keys  :: (list[number])             => set[number]  */
/*@ measure keysp :: (<l> + null, list[number]) => set[number]  */
/*@ measure keysp(p,x) = (if (p = null) then (Set_sng(0) ∩ Set_sng(1)) else keys(x)) */

/*@ consSorted ::
  (p:<p>, k:number)/p |-> ps:list[{number | v > k}]<{\h v -> h <= v}>
   => {v:<l> | keysp(v,ls) = Set_cup(Set_sng(k), keysp(p,ps))} /l |-> ls:list[number]<{\h v -> h <= v}>*/
function consSorted(p,k) {
  var y = {};
  y.data = k;
  y.next = p;
  return y;
}
