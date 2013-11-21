//import "singly-linked-list.js"

/*@ reverseLoop :: forall A. (i:<i>+null, j:<j>+null)/i |-> is:list[A] * j |-> js:list[A]
                                 => {v:<k>+null | ((v = null) <=> ((i = null) && (j = null)))}/
                                 k |-> {list[A] | (if (i = null)
                                                      then ((len(v) = len(js)) && (keys(v) = keys(js)))
                                                      else (if (j = null)
                                                               then ((len(v) = len(is)) && (keys(v) = keys(is)))
                                                               else ((len(v) = len(is) + len(js))
                                                                  && (keys(v) = Set_cup(keys(is), keys(js))))))}
*/
function reverseLoop(i, j){
  if (i != null) {
    var temp = i.next;
    i.next   = j;
    var r    = reverseLoop(temp, i);
    return r;
  } else {
    return j;
  }
}

/* reverse :: (x:list[A])/h => {v:list[A]}/v |-> keys(v) = keys(x,h) */

/*@ reverse :: forall A. (x:<x>)/x |-> xs:list[A] => <y>/y |-> ys:list[{A | true}]*/
function reverse(x){
  var y = null;
  var r = reverseLoop(x,y);
  return r;
}

