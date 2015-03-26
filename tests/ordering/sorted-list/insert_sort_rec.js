/*@ include sorted-list.js */

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

/*@ insertion_sort ::  forall A.
  (x:{v:<l>+null | true})/l |-> ls:list[A]<{\h v -> true }>
    => v:<k>+null/k |-> ys:list[A]<{\h v -> h <= v}>  */
function insertion_sort(x){
  if (x == null) return null;

  var xn = x.next;
  var xk = x.data;
  var t  = insertion_sort(xn);
  return insert(t, xk);
}