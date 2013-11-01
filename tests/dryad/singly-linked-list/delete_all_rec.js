//import "singly-linked-list.js"

/*@ remove :: forall A. (x:<l>+null, k:A)/l |-> as:list[A]
                              => {v:<m>+null | ((ttag(v) = "null") <=> ((keys(as) = Set_sng(k)) || (ttag(x) = "null"))) }
                                  /m |-> bs:{list[A] | (if (ttag(lqreturn) != "null")
                                                           then (keys(v) = Set_dif(keys(as), Set_sng(k)))
                                                           else (Set_emp(keys(v))))} */
function remove(x, k){
  if (typeof(x) != "null") {
    var xn = x.next;
    var t = remove(xn, k);
    x.next = t;
    var d = x.data;
    if (d == k) {
      return t;
    } else {
      return x;
    }
  } else {
    return null;
  } 
}
