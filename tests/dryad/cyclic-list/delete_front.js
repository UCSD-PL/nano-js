/*@ include cyclic_list.js */

/*@ remove :: (x:{v:<x> | true})/x |-> xs:{data:number, next:either[<y>,<x>]} * y |-> clist[number,<x>]
                    => {v:<x>+null | (ttag(field_T(xs,"next")) = "inl" <=> (v != null))}
                       /x |-> ys:{data:number, next:either[<z>,<x>]} * z |-> clist[number,<x>] */
function remove(x){
  var xn = x.next;
  if (isL(xn)) {
    var t  = projL(xn);
    var u  = t.next;
    x.next = u;
    return x;
  } else {
    return null;
  }
}
