/*@ include sorted-list.js */

/*@ insert :: forall A.
  (x:<l>+null, k:A)/l |-> ls:incList[A]
      => {v:<k> | ((keysp(v,ks) = Set_cup(Set_sng(k),keysp(x,ls)))
                && (lenp(v,ks) = 1 + lenp(x,ls)))}
         /k |-> ks:incList[A] */
function insert(x, k){
  if (x == null){
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
