/*@ include sorted-list.js */

/*@ insert :: forall < p :: (number) => prop >.
  (x:<l>+null, k:number<p>)/l |-> ls:list[number<p>]<{\h v -> h <= v}>
       => {v:<k> | ((lenp(v,ks) = 1 + lenp(x,ls)) 
                 && (keysp(v,ks) = Set_sng(k) ∪ keysp(x,ls)))}
          /k |-> ks:list[number<p>]<{\h v -> h <= v}>
*/
function insert(x, k){
  if (x == null){
    var y  = { data:k, next: null };
    return y;
  } else {
    var xk = x.data;
    if (k <= xk){
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

/*@ insertion_sort :: forall < p :: (number) => prop >.
  (x:<l>+null)/l |-> ls:list[number<p>]<{\h v -> true}>
    => {v:<k>+null | (lenp(v,ks) = lenp(x,ls)
                   && keysp(v,ks) = keysp(x,ls)) }/k |-> ks:list[number<p>]<{\h v -> h <= v}>  */
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
