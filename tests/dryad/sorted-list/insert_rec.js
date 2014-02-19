/*@ include sorted-list.js */

/*@ qualif Ret(v:a): (lenp(v,ys) = 1 + lenp(x,xs)) */
/*@ qualif Ret(v:a): (keysp(v,ys) = (Set_cup(keysp(x,xs), Set_sng(k)))) */

/*@ insert :: forall A.
  (x:<l>+null, k:A)/l |-> xs:list[A]<{\h v -> true}>
             => <k>/k |-> ys:list[A]<{\h v -> true}>
*/
function insert(x, k){
  if (x == null){
    var y  = { data:k, next: null };
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
