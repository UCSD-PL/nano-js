/*@ include singly-linked-list.js */

/*@ insert :: 
  (x:<l>+null, k:number)/l |-> xs:list[number]
    => <m>/m |-> ys:{v:list[number] | ((len(v) = 1 + len(xs)) && (keys(v) = Set_cup(Set_sng(k),keys(xs))))}
*/
function insert(x, k){
 if (x != null){
    var n = x.next;
    var t = insert(n, k);
    x.next = t;
    return x;
 }

 var y  = {data:k, next:x};
 return y;
}
