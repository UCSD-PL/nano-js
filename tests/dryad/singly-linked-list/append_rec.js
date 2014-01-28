/*@ include singly-linked-list.js */

/*@ append :: (x1:<l>+null, x2:<m>+null)/l |-> x1s:list[number] * m |-> x2s:list[number]
               => {v:<k>+null | ((lenp(v,ks) = lenp(x1,x1s) + lenp(x2,x2s))
                              && (keysp(v,ks) = keysp(x1,x1s) ∪ keysp(x2,x2s)))}
                  /k |-> ks:list[number]
*/
function append(x1, x2){
  if (x1 != null){
      var n = x1.next;
      x1.next = append(n, x2);
      return x1;
  } else {
      return x2;
  } 
}
