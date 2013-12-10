//import "singly-linked-list.js"
/*@
  assert_zero :: forall A.
    (x:{v:<l>+null | lenp(v,xs) = 0})/l |-> xs:list[A] => void/same
*/

/*@ insert :: forall A.
  (x:<l>+null, k:A)/l |-> xs:list[A]
                => {v:<m> | ((lenp(v,ys) = 1 + lenp(x,xs))
                          && (keysp(v,ys) = Set_cup(Set_sng(k),keysp(x,xs)))) }
                   /m |-> ys:list[A]
*/
function insert(x, k){
  if (x != null){
    var n = x.next;
    var t = insert(n, k);
    x.next = t;
    return x;
  }
  else
  {
    assert_zero(x);
    var y  = {}; // {data : k, next : null };
    y.data = k;
    y.next = null;
    return y;
  }
}
