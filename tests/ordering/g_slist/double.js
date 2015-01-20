/*@ include sorted-list.js */


/*@ doubl :: forall A. (x:A) => {v:A | v = 2*x} */

/*@ inc_while_loop :: forall A.
        (x:<l>+null,k:A)/l |-> x1:list[A]<{\h v -> true}> => 
        <m>+null/l |-> x2:list[A]<{\h v -> true}> 
               * m |-> y0:list[A]<{\h v -> true}> */
function inc_while_loop(x,k) {
  if (x != null) {
    var k2 = x.data;
    var xn = x.next;
    var yn = inc_while_loop(xn,k2);
    var k = doubl(k);
    var y = { data:k, next:yn };
    return y;
  } else {
    return null;
  }
}

/* double :: ... incList[number] => incList[number] */

/*@ double :: forall A.
     (x:<l>+null)/l |-> x0:list[{v:A | v > 0}]<{\h v -> h <= v}> => 
      {v:<m>+null | true }/l |-> x1:list[A]<{\h v -> h <= v}> 
                         * m |-> y0:list[A]<{\h v -> h <= v}> */
function double(x) {
  if(x != null) {
    var k = x.data;
    var xn = x.next;
    var yn = inc_while_loop(xn,k);
    k = doubl(k);
    y = { data: k, next:yn };
    return y;
  } else {
    return null;
  }
}
