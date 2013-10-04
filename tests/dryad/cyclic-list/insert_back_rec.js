// DROP the refinement on the output. the dryad postcondition is lame (and has 
// no mention of keys.

/*@ insert :: (p:clist[A,<q>], {q:clist[A,<q>] | q != p}, k:A) 
           => void/p |-> {clist[A,<q>] | keys(p) = set_cup(keys(p,h),set_singleton(k))} 
 */

function insert(p, q, k){
  var t = p.next;
  if (t == q) {
    // p.next == q
    var z  = {};
    z.data = k;
    z.next = q;
    p.next = z;
  } else {
    // p.next != q
    p.next = insert(t, q, k);
  }
}
