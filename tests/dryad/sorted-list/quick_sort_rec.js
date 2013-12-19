/*@ include sorted-list.js */
/*@ qualif AppKeys(v:a) : keys(v) = Set_cup(keysp(ls,ll),keysp(gs,gg)) */

/*@ append :: forall A.
  (xk:A, ls:<l>+null, gs:<g>+null)/l |-> ll:incList[{A | v <  xk }]
                                 * g |-> gg:incList[{A | v >= xk }]
    => {v:<k>+null | keysp(v,kk) = Set_cup(keysp(ls,ll),keysp(gs,gg)) }
       /k |-> kk:incList[A]                                             */
function append(xk, ls, gs) {
  if (ls == null) {
    return gs;
  }

  var n = ls.next;
  if (n == null) {
    ls.next = gs;
  } else {
    n = append(xk, n, gs);
    ls.next = n;
  }
  return ls;
}

/*@ nullList :: forall A. (A) => {v:<l>+null | v = null}/l |-> list[A] */

/*@ partition :: forall A.
   (piv:A, x:<x>+null)/x |-> xs:list[A]
     => {v:<r> | keysp(x,xs) = Set_cup(keysp(field(p,"x"),as),keysp(field(p,"y"),bs))}
                 /a |-> as:list[{A | v < piv}]
                * b |-> bs:list[{A | v >= piv}]
                * r |-> p:{x:<a>+null, y:<b>+null}                                  */
function partition(piv, x){
  if (x == null) {
      var ret = {};
      ret.x = null;
      ret.y = null;
      return ret;
  }

  var xn = x.next;
  var yz = partition(piv, xn);
  var xd = x.data;
  var a = yz.x;
  var b = yz.y;
  if (cmpLT(xd,piv)){
    x.next = a
    var ret = {};
    ret.x = x;
    ret.y = b;
    return ret;
  } else {
    x.next = b;
    var ret = {};
    ret.x = a;
    ret.y = x;
    return ret;
  }
}

/*@ quickSort :: forall A.
      (x:<x>+null)/x |-> in:list[A]
        => {v:<o>+null | keysp(v,out) = keysp(x,in) }
          /o |-> out:incList[A] */
function quickSort(x) {
  if (x == null){
    return null;
  }
  var piv = x.data;
  var xn  = x.next;
  var yz  = partition(piv, xn);
  var ls  = quickSort(yz.x);
  var gs  = quickSort(yz.y);
  x.next  = gs;
  var ret = append(piv, ls, x);
  return ret;
}

