/*@ type list[A]<p :: (A, A) => prop>
        exists! l |-> tl:list[A<p data>]<p>. 
          r:{ data : A, next : <l> } */

/*@ qualif QApp(v:a) : papp1(q, v) */

/*@ consSorted :: forall A.
  (p:{v:<p> | true}, k:A)/p |-> ps:list[A]<{\x y -> x <= y}>
                           => <l>/l |-> ls:list[A]<{\x y -> x <= y}> */
function consSorted(p, k) {
  var d = p.data;

  if (d < k) {
    var n = p.next;
    p.next = consSorted(n, k);
  }

  return p;
}
  
