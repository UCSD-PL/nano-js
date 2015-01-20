/*@ include list.js */

/*@ qualif LenEq(v:T,p:Ref,x:T): lenp(p,v) = lenp(p,x) */
/*@ qualif Len(v:number,p:Ref,x:T): v = lenp(p,x) */

/*@ len_loop :: 
      forall A. (l:<l>+null)/l |-> l0:list[A] => number/l |-> l1:list[A] */
function len_loop(l) {
  if (l == null) {
    return 0;
  } else {
    var ln = l.next;
    var n  = len_loop(ln); 
    return 1 + n;
  }
}

/*@ getLength ::
      forall A. (l:<l>+null)/l |-> l0:list[A] => {v:number | v = lenp(l,l0)}/l |-> l1:list[A] */
function getLength(l) {
  var x = len_loop(l);
  return x;
}
