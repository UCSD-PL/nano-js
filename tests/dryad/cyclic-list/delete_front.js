//import "cyclic-lists.js";

/*@ remove :: forall A. (x:<x>)/x |-> xs:clist[A,<x>]
                    => {v:<x>+null | ((len(xs) > 1) => (ttag(v) != "null"))}
                       /x |-> ys:{clist[A,<x>] | (&& ((len(xs) > 1) => (len(v) = len(xs) - 1))}*/
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
