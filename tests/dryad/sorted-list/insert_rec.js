/*@ include sorted-list.js */

/*@ insert :: forall A.
  (x:<l>+null, k:A)/l |-> xs:list[A]<{\h v -> h <= v}> =>
             <k>/k |-> ys:{v:list[A]<{\h v -> h <= v}> | len(v) = len(xs) + 1}
*/
function insert(x, k){
  if (x == null){
    var y = { data:k, next:null };
    return y;
  } else {
    var xk = x.data;
    if (k <= xk) {
      var y  = {data: k, next: x};
      return y;
    } else {
      var y = x.next;
      var t = insert(y, k);
      x.next = t;
      return x;
    }
  }
}
