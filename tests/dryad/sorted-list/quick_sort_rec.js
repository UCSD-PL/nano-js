/*@ include sorted-list.js */
/*@ qualif AppKeys(v:a) : keys(v) = Set_cup(keysp(ls,ll),keysp(gs,gg)) */

/*@ append :: forall <p :: (number) => prop>.
  (xk:number, ls:<l>+null, gs:<g>+null)/l |-> ll:list[{v:number<p> | v <  xk}]<{\h v -> h <= v}>
                                 * g |-> gg:list[{v:number<p> | v >= xk}]<{\h v -> h <= v}>
    => {v:<k>+null | keysp(v,kk) = Set_cup(keysp(ls,ll),keysp(gs,gg)) }
       /k |-> kk:list[number<p>]<{\h v -> h <= v}>                                             */
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
/*@ qualif PApp(v:a): (papp1 p v) */

/*@ partition :: forall <p :: (number) => prop >.
   (piv:number, x:<x>+null)/x |-> xs:list[number<p>]<{\h v -> true}>
     => {v:<r> | keysp(x,xs) = Set_cup(keysp(field(p,"x"),as),keysp(field(p,"y"),bs))}
                 /a |-> as:list[{v:number<p> | piv >  v}]<{\h v -> true}>
                * b |-> bs:list[{v:number<p> | piv <= v}]<{\h v -> true}>
                * r |-> p:{x:<a>+null, y:<b>+null}                */
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
  if (xd < piv){
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

/*@ quickSort :: forall <p:: (number) => prop>.
      (x:<x>+null)/x |-> in:list[number<p>]<{\h v -> true}>
        => {v:<o>+null | keysp(v,out) = keysp(x,in) }
          /o |-> out:list[number<p>]<{\h v -> h <= v}> */
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
