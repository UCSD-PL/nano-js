
/*@ insert :: (x:clist[A,<x>], k:A) 
           => <ret>/ x |-> {data: A, next: <ret>} * ret |-> clist[A, <x>]
 */

function insert(x, k){
  var t  = x.next;
  var z  = {};
  z.data = k;
  z.next = t;
  x.next = z;
  return z;
}
