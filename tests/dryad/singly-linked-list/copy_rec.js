/*@ include singly-linked-list.js */

/*@
  copy ::
    (x:<l>+null)/l |-> xs:list[number]
      => {v:<m>+null | ((lenp(v,ms) = lenp(x,xs))
                     && (keysp(v,ms) = keysp(x,xs)))}
        /l |-> xss:list[number] * m |-> ms:list[number]
*/
function copy(x){
  if (x == null){
    var ret = null;
    return ret;
  }
  var u  = copy(x.next);
  var t  = {data: x.data, next: u};
  return t;
}

