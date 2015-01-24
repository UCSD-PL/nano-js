/*@ include singly-linked-list.js */

/*@ append :: (x1:<l>+null, x2:<m>+null)/l |-> x1s:list[number] * m |-> x2s:list[number]
               => {v:<k>+null | (Prop(nil(v)) => (Prop(nil(x1)) && Prop(nil(x2))))}
                  /k |-> ks:{v:list[number] | ((keys(v) = Set_cup(keys(x1s),keys(x2s))) && (len(v) = len(x1s) + len(x2s)))}
*/
function append(x1, x2){
  if (x1 != null){
    var n = x1.next;
    var nn = append(n, x2);
    x1.next = nn;
    return x1;
  } else {
    return x2;
  } 
}

/*@ qualif EqNil(v:a, x:b): ((x != null) => (v = 0)) */
/*@ to_zeroes :: (<l>)/l |-> xs:list[{v:number|v = 1}] => void/l |-> ys:list[{v:number | v = 0 }] */
function to_zeroes(x) {
   var n = x.next;
   x.data = 0;

   if (n != null) {
     to_zeroes(n);
   } 

   return;
}
