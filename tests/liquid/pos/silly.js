/*@ measure val :: (t[A]) => A */
/*@ type t[A]<p :: (t[A], A) => prop> 
      exists! l |-> eks:t[A]<p>. foo:{ data:A<p eks>, next:<l> }
      with val(zzz) = field(foo, "data")
*/

/*@ qualif EqVal(v:a, x:b): v = val(x) */

/*@ bar :: (x:<l>)/l |-> in:t[number]<{\h v -> true}> 
    => {v:number | v = val(out)}/l |-> out:t[number]<{\h v -> v = val(h)}> */
function bar(x) {
  var next = x.next;
  var y    = bar(next);
  x.data   = y;

  return y;
}
