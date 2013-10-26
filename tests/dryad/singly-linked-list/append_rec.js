//import "singly-linked-list.js"

// In below, separation between x and v in output IS obvious.
/* append_desired::(x1:<l>+null,x2:<m>+null)/h => {v:list[A]}/ v |-> keys(v) = set_cup(keys(x1,h), keys(x2,h)) */

/*@ append:: forall A. (x1:<l>+null,x2:<m>+null)/l |-> xs:list[A] * m |-> ys:list[A]
                                  => {v:<k>+null | (((ttag(x1) != "null") || (ttag(x2) != "null")) <=> (ttag(v) != "null"))}
                                     /k |-> zs:{list[A] | (if (ttag(x1) != "null") 
                                                           then (if (ttag(x2) != "null")
                                                                 then (len(v) = len(xs) + len(ys))
                                                                 else (len(v) = len(xs)))
                                                           else (if (ttag(x2) != "null")
                                                                 then (len(v) = len(ys))
                                                                 else true))}
*/
function append(x1, x2){
  if (typeof(x1) != "null"){
      var n = x1.next;
      x1.next = append(n, x2);
      return x1;
  } else {
      return x2;
  } 
}
