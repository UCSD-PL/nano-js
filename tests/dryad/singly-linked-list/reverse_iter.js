//import "singly-linked-list.js"

/* reverseLoop :: (i:<i>, j:<j>)/i |-> list[A] * j |-> list[A]
      => j |-> {v:list[A]}/v |-> keys(v) = set_cup(keys(i,h), keys(j,h)) */

/*@ reverseLoop :: forall A. (i:<i>+null, j:<j>+null)/i |-> is:list[A] * j |-> js:list[A]
                                 => {v:<k>+null | ((ttag(v) = "null") <=> ((ttag(i) = "null") && (ttag(j) = "null")))}/
                                 k |-> {list[A] | (if (ttag(i) = "null")
                                                      then (len(v) = len(js))
                                                      else (if (ttag(j) = "null")
                                                               then (len(v) = len(is))
                                                               else (len(v) = len(is) + len(js))))}
*/
function reverseLoop(i, j){
  if (typeof(i) != "null") {
    var temp = i.next;
    i.next   = j;
    var r    = reverseLoop(temp, i);
    return r;
  } else {
    return j;
  }
}

/* reverse :: (x:list[A])/h => {v:list[A]}/v |-> keys(v) = keys(x,h) */

// /*@ reverse :: forall A. (x:<x>)/x |-> list[A] => <x>/same */
// function reverse(x){
//   var y = null;
//   return reverseLoop(x,y);
// }

