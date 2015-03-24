/*@ include sorted-list.js */

/*@ qualif Sum(v:number, x:number, y:number): (v >= x + y) */

/*@ pairwise_loop ::
  (x : <l>+null, xk:number, y : <m> + null, yk:number)/l |-> x0:list[number]<{\h v -> h <= v}>
                               * m |-> y0:list[number]<{\h v -> h <= v}> =>
                           <r>+null/r |-> r1:list[number]<{\h v -> h <= v}>
                                  * l |-> x1:list[number]<{\h v -> h <= v}>
                                      * m |-> y1:list[number]<{\h v -> h <= v}>  */
function pairwise_loop(x,xk,y,yk) {
  if (x == null) 
    return null;
  if (y == null)
    return null;
  zk = xk + yk;
  xk = x.data;
  yk = y.data;
  xn = x.next;
  yn = y.next;
  zn = pairwise_loop(xn,xk,yn,yk);
  z = { data:zk, next:zn };
  return z;
}

/*@ 
pairwise::
  (x : <l>+null, y : <m>+null)/l |-> x0:{v:list[number]<{\h v -> h <= v}> | (len(v) = len(y0))}
                             * m |-> y0:list[number]<{\h v -> h <= v}>  => 
                           <r>+null/r |-> r1:{v:list[number]<{\h v -> h <= v}> | (len(v) = len(x1))}
                                  * l |-> x1:list[number]<{\h v -> h <= v}>
                                  * m |-> y1:list[number]<{\h v -> h <= v}>  
*/  
function pairwise(x,y) {
  if (x == null)
    return null;

  if (y == null)
    return null;

  var xk = x.data;
  var xn = x.next;
  var yk = y.data;
  var yn = y.next;
  var rn = pairwise_loop(xn,xk,yn,yk);
  var rk = xk + yk;
  var r = { data:rk, next:rn };
  return r;
}
