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
