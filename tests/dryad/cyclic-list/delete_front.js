import "cyclic-lists.js";

/*@ remove :: (x:clist[A,<x>]) => {v:?clist[A,v]} */

function remove(x){
  if (x.next == x) {
    return null;
  } else {
    var t  = x.next;
    var u  = t.next;
    x.next = u;
    return x;
  }
}
