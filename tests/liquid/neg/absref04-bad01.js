/*@
type list[A]<p :: (A, A) => prop>
        exists! l |-> tl:list[A<p (field r "data")>]<p>. 
          r:{ data : A, next : <l> + null }

*/

/*@ consSorted :: (p:<p>, k:number)/p |-> ps:list[{number | true}]<{\h v -> h <= v}>
                         => <l>/l |-> ls:list[number]<{\h v -> h <= v}> */
function consSorted(p,k) {
  var y = {};
  y.data = k;
  y.next = p;
  return y;
}
