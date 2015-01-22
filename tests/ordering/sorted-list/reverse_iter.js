/*@ include sorted-list.js */

/*@ reverseLoop :: forall A.
  (i:<i>+null, a:A, j:<j>+null)/i |-> is:list[A]<{\h v -> h <= v}> 
                              * j |-> js:list[A]<{\h v -> h <= v}>
    => <k>+null/k |-> ks:list[A]<{\h v -> v <= h}>                  */
function reverseLoop(i, a, j){
  if (i != null) {
    var temp = i.next;
    var d    = i.data;
    i.next   = j;
    var z = i; // hehehe bug otherwise :(
    var r    = reverseLoop(temp, d, z);
    return r;
  } else {
    return j;
  }
}

/*@ reverse ::
  (x:{v:<x> | true})/x |-> xs:list[number]<{\h v -> h <= v}> => 
    {v:<y>+null | lenp(v,ys) = lenp(x,xs) }/y |-> ys:list[number]<{\h v -> v <= h}> */
function reverse(x){
  xk = x.data;
  xn = x.next;
  x.next = null;
  var r = reverseLoop(xn,xk,x);
  return r;
}

