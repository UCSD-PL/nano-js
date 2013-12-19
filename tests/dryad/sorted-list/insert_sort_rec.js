/*@ include sorted-list.js */

/*@ insert :: forall A.
  (x:<l>+null, k:A)/l |-> ls:incList[A]
      => {v:<k> | (keysp(v,ks) = Set_cup(Set_sng(k),keysp(x,ls))
                && lenp(v,ks) = 1 + lenp(x,ls))}
         /k |-> ks:incList[A] */

function insert(x, k){
  if (x == null) {
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

/*@ insertion_sort :: forall A.
  (x:<l>+null)/l |-> ls:list[A]
    => {v:<k>+null | (lenp(v,ks) = lenp(x,ls)
                   && keysp(v,ks) = keysp(x,ls)) }/k |-> ks:incList[A]  */
function insertion_sort(x){
  if (x == null){
      return null;
  } else {
      var xn = x.next;
      var xk = x.data;
      var t  = insertion_sort(xn);
      return insert(t, xk);
  }
}
