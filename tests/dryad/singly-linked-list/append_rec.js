//import "singly-linked-list.js"

// In below, separation between x and v in output IS obvious.
/* append_desired::(x1:<l>+null,x2:<m>+null)/h => {v:list[A]}/ v |-> keys(v) = set_cup(keys(x1,h), keys(x2,h)) */

/*@ append:: forall A. (x1:<l>+{null | true},x2:<m>+null)/l |-> list[A] * m |-> list[A] => <k>+null/k |-> list[A] */
function append(x1, x2){
  if (typeof(x1) != "null"){
    var n = x1.next;
    append(n, x2);
    x1.next = n;
    return x1;
  } else {
    return x2;
  } 
}
