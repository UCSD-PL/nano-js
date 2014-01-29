/*@ include cyclic_list.js */



/*@ insert :: 
      (x:<x>, k:number)/x |-> xs:clist[number,<x>]
        => void/x |-> ys:{v:clist[number,<x>] | ((keys(v) = Set_cup(Set_sng(k), keys(xs)))
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
