/*@ include sorted-list.js */


/* qualif D(v:number, x:number): v >= 2*x */
/*@ qualif Sum(v:number, x:number, y:number): (v >= x + y) */

/*@ inc_while_loop :: 
        (x:<l>+null,k:number)/l |-> x1:list[number]<{\h v -> h <= v}> => 
        <m>+null/
                 l |-> x2:list[number]<{\h v -> h <= v}>
               * m |-> y0:list[number]<{\h v -> h <= v}> */
function inc_while_loop(x,k) {
  if (x != null) {
    var k2 = x.data;
    var xn = x.next;
    var yn = inc_while_loop(xn,k2);
    var kk = k + k; //doubl(k);
    var y = { data:kk, next:yn };
    return y;
  } else {
    return null;
  }
}

/*@ double :: 
     (x:{v:<l>+null | true})/l |-> x0:list[number]<{\h v -> h <= v}> => 
      <m>+null/l |-> x1:{v:list[number]<{\h v -> h <= v}> | (len(v) = len(x0))} 
             * m |-> y0:{v:list[number]<{\h v -> h <= v}> | (len(v) = len(x0))}
             */
function double(x) {
  if(x != null) {
    var k = x.data;
    var xn = x.next;
    var yn = inc_while_loop(xn,k);
    k = k + k;
    y = { data: k, next:yn };
    return y;
  } else {
    return null;
  }
}
