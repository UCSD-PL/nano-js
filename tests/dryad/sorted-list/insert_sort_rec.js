//import "sorted-list.js";

/* insert :: (x:?incList[A], k:A) => incList[A] */

/* insert :: (x:?incList[A], k:A) => <l>/l|-> {v:incList[A] | SetPlus(keys(v), keys(x,h), k) } */

/*@ insert :: (x:{v:<l> | true} + {null | true}, k:number)/l |-> list[number] => <k>/k |-> list[{number | true}] */
function insert(x, k){
  if (typeof(x) == "null"){
    // x == null
    var y  = {};
    y.data = k;
    y.next = null;
    return y;
  } else {
    var xk = x.data;
    if (k <= xk){
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

/*@ insertion_sort :: (<l>+null)/l |-> list[number] => <k>+null/k |-> list[{ number | true }] */
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
