/*@ include doubly-linked-list.js */
/*@ qualif EqMeas(v:T, vs:T): (len(v) = len(vs)) */
/*@ qualif EqMeas(v:T, vs:T): (keys(v) = keys(vs)) */

/*@
  insert ::
    (x:<x>+null, k:number)/x |-> xs:dlist[number,<x>,null]
       => r:<j>/j |-> js:{v:dlist[number,<j>,null] | ((len(v) = 1 + len(xs)
&& (keys(v) = Set_cup(Set_sng(k),keys(xs)))))}
*/
function insert(x, k){
  var y  = {data:k, next:x, prev:null};

  if (x != null) {
    y.next = x;
    x.prev = y;
  }

  return y;
}

