/*@ include cyclic_list.js */

/*@ remove :: (x:<x>)/x |-> xs:clist[number,<x>]
                    => {v:<x>+null | ((len(xs) > 1) => (v != null))}
                       /x |-> ys:{v:clist[number,<x>] | ((len(xs) > 1) => (len(v) = len(xs) - 1))} */
function remove(x){
  var xn = x.next;
  if (isL(xn)) {
    var t  = projL(xn);
    var u  = t.next;
    x.next = u;
    return x;
  } else {
    return null;
  }
}
