/*@ type list[A]<p :: (A, A) => prop>
        exists! l |-> tl:list[A<p (field r "data")>]<p>. 
          r:{ data : A, next : <l> } */

/*@ qualif QApp(v:a) : papp1(q, v) */

/*@ consSorted :: forall < q :: (number) => prop >.
  (p:{v:<p> | true}, k:number<q>)/p |-> ps:list[number<q>]<{\x y -> x <= y}>
              => <l>/l |-> ls:list[number<q>]<{\x y -> x <= y}> */
function consSorted(p, k) {
 d = p.data;

  if (0 > d) { // better not prove q...
    var n = p.next;
    p.next = consSorted(n, 0);
  }

  return p;
}
  
