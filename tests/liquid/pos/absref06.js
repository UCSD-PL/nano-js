/*@ type list[A]<p :: (A, A) => prop>
        exists! l |-> tl:list[A<p (field r "data")>]<p>. 
          r:{ data : A, next : <l> } */

/*@ qualif QApp(v:a) : papp1(q, v) */

/*@ consSorted :: forall < q :: (number) => prop >.
  (p:{v:<p> | true}, k:number<q>)/p |-> ps:list[number<q>]<{\x y -> x <= y}>
                               => <l>/l |-> ls:list[number<q>]<{\x y -> x <= y}> */
function consSorted(p, k) {
  var d = p.data;

  if (d < k) {
    var n = p.next;
    p.next = consSorted(n, k);
  }

  return p;
}
  
