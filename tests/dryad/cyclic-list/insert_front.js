//import "cyclic_lists.js";



/*@ insert :: forall A H. (x:<x>, k:A)/x |-> xs:clist[A,<x>]
                                => void/x |-> ys:{clist[A,<x>] | ((keys(v) = Set_cup(Set_sng(k), keys(xs)))
                                                                 && (len(v) = len(xs) + 1))}
 */
function insert(x, k){
  var z  = {};
  t = x.next;
  z.data = k;
  z.next = t;
  x.next = inL(z);
  return;
}
