import "sorted-list.js";


/*@ insert :: (x:?incList[A], k:A) => incList[A] */

/*@ insert :: (x:?incList[A], k:A) => <l>/l|-> {v:incList[A] | SetPlus(keys(v), keys(x,h), k) } */

function insert(x, k){
  if (x == null){
    // x == null
    var y  = {};
    y.data = k;
    y.next = null;
    return r;
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
