/*@ include singly-linked-list.js */

/*@
  copy :: forall A.
    (x:<l>+null)/l |-> xs:list[A]
      => {v:<m>+null | ((lenp(v,ms) = lenp(x,xs))
                     && (keysp(v,ms) = keysp(x,xs)))}
        /l |-> xss:list[A] * m |-> ms:list[A]
*/
function copy(x){
  if (x == null){
    var ret = null;
    return ret;
  } else {
    var u  = copy(x.next);
    var d  = x.data;
    var n  = u;
    var t  = {data: d, next: n};
    return t;
  } 
}

