//import "singly-linked-list.js"

/*@ zeroln :: forall A. (x:{v:<l>+null | lenp(v,xs) = 0})/l |-> xs:list[A] => void/same */

/*@ insert :: forall A. (x:<l>+null, k:A)/l |-> xs:list[A] =>
                                      {v:<m> | ((lenp(v,ys) = lenp(x,xs) + 1))}
                                      /m |-> ys:list[A]
*/
                                             //&& (keysp(v,ys) = Set_cup(Set_sng(k),keysp(x,ls))))}
function insert(x, k){
  if (x != null){
    var n = x.next;
    var t = insert(n, k);
    x.next = t;
    return x;
  }
  else
  {
    var y  = {}; // {data : k, next : null };
    y.data = k;
    y.next = x; //null
    return y;
  }
}
