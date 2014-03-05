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

/*@ insertion_sort ::  forall A.
  (x:<l>+null)/l |-> ls:list[A]<{\h v -> true}>
    => {v:<k>+null | (lenp(v,ys) = lenp(x,ls) 
                  && (keysp(v,ys) = keysp(x,ls))) }/k |-> ys:list[A]<{\h v -> h <= v}>  */
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
