//import "singly-linked-list.js"

/* reverseLoop :: (i:<i>, j:<j>)/i |-> list[A] * j |-> list[A]
      => j |-> {v:list[A]}/v |-> keys(v) = set_cup(keys(i,h), keys(j,h)) */

/*@ reverseLoop :: forall A. (i:<i>+null, j:<j>+null)/i |-> list[{A|true}]
                                                    * j |-> list[A] => <k>+null/k |-> list[A] */
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

