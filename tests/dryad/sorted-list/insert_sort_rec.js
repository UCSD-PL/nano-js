/*@ insert :: forall A. (x:<l>+null, k:A)/l |-> in:sList[A]
                                   => <k>/k |-> out:{sList[A]
                                               | (if (ttag(x) != "null")
                                                      then ((if (min(in) < k)
                                                           then (min(v) = min(in))
                                                           else (min(v) = k))
                                                             && (keys(v)= Set_cup(Set_sng(k), keys(in))
                                                             && (len(v) = len(in) + 1)))
                                                      else ((min(v)  = k)
                                                         && (keys(v) = Set_sng(k))
                                                         && (len(v)  = 1))) } */

function insert(x, k){
  if (typeof(x) == "null"){
    // x == null
    var y  = {};
    y.data = k;
    y.next = null;
    return y;
  } else {
    var xk = x.data;
    if (cmp(k,xk)){
      var y  = {};
      y.data = k;
      y.next = x;
      return y;
    } else {
      var y = x.next;
      var t = insert(y, k);
      x.next = t;
      return x;
    }
  }
}

/*@ insertion_sort :: forall A. (x:<l>+null)/l |-> ls:list[A]
                          => {v:<k>+null | ((ttag(v) != "null") <=> (ttag(x) != "null"))}
                                          /k |-> ks:{sList[A] | (if (ttag(lqreturn) != "null")
                                                                    then ((len(v) = len(ls)) && (keys(v) = keys(ls)))
                                                                    else true)}
*/
function insertion_sort(x){
  if (typeof(x) == "null"){
      return null;
  } else {
      var xn = x.next;
      var xk = x.data;
      var t  = insertion_sort(xn);
      var u  = insert(t, xk);
      return u;
  }
}
