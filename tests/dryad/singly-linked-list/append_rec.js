import "singly-linked-list.js"

// In below, separation between x and v in output IS obvious.
/*@ append::(x1:list[A],x2:list[A])/h => {v:list[A]}/ v |-> keys(v) = set_cup(keys(x1,h), keys(x2,h)) */

function append(x1, x2){
  if (!x1){
    return x2;
  } else {
    var t = append(x1.next, x2);
    x1.next = t;
    return x1;
  } 
}
