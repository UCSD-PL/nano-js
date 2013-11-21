//import "singly-linked-list.js"

/*@ remove :: forall A. (x:<l>+null, k:A)/l |-> as:list[A]
                              => {v:<m>+null | ((v = null) <=> ((keys(as) = Set_sng(k)) || (x = null))) }
                                  /m |-> bs:{list[A] | (if (lqreturn != null)
                                                           then (keys(v) = Set_dif(keys(as), Set_sng(k)))
                                                           else (Set_emp(keys(v))))} */
function remove(x, k){
  if (x != null) {
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
