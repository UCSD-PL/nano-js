import "singly-linked-list.js"

/*@ reverseLoop :: (i:list[A], j:list[A])/h 
      => {v:list[A]}/v |-> keys(v) = set_cup(keys(i,h), keys(j,h)) */

function reverseLoop(i, j){
  if (i) {
    var temp = i.next;
    i.next = j;
    return reverseLoop(temp, i);
  } else {
    return j;
  }
}

/*@ reverse :: (x:list[A])/h => {v:list[A]}/v |-> keys(v) = keys(x,h) */

function reverse(x){
  return reverseLoop(x,null);
}

