/*@ include singly-linked-list.js */

/*@
  copy ::
    (x:<l>+null)/l |-> xs:list[number]
      => {v:<m>+null | (((Prop(nil(v)) <=> (Prop(nil(x))))))}/l |-> xss:{v:list[number] | ((Prop(nil(v)) <=> Prop(nil(xs))) && (len(v) = len(xs)) && (keys(v) = keys(xs)))} * m |-> ms:{v:list[number] | ((len(v) = len(xs)) && (keys(v) = keys(xs)))}
*/
function copy(x){
  if (x == null){
    return null;
  }
  var u  = copy(x.next);
  var d  = x.data;
  var t  = {data: d, next: u};
  return t;
}

