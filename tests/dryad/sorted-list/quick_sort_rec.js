//import "sorted-list.js";

// NOT IN DRYAD

/*@ qualif Gross(v:a, x:b): (v >= field(x, "data")) */
/*@ qualif Gross(v:a, x:b): (v >= min(x)) */
/*@ qualif Gross(v:a, x:b): (min(v) >= min(x)) */

/*@  append :: forall A. (xk:A, ls:<l>+null, gs:<m>+null)/l |-> ll:sList[{A | v <  xk }]
                                                        * m |-> mm:sList[{A | v >= xk }]
                                              => <k>+null/k |-> kk:{sList[A] | ((min(v) = min(ll)) || (v = mm)) }*/
function append(xk, ls, gs) {
  if (typeof(ls) == "null") {
    return gs;
  }

  var n = ls.next;
  if (typeof(n) == "null") {
    ls.next = gs;
    return ls;
  } else {
    var x = n.data;
    n = append(xk, n, gs);
    ls.next = n;
    return ls;
  }
}

/*@ partition :: forall A.
   (piv:{A | true}, x:<x>+null)/x |-> list[A] => <r>/r |-> {x:<a>+null, y:<b>+null}
                                                   * a |-> list[{A | v < piv}]
                                                   * b |-> list[{A | v >= piv}] */  
function partition(piv, x){
  if (typeof(x) == "null") {
      var ret = {x:null, y:null};
      return ret;
  }

  var xn = x.next;
  var yz = partition(piv, xn);
  var xd = x.data;
  var a = yz.x;
  var b = yz.y;
  if (cmpLT(xd,piv)){
    x.next = a
    var ret = {x:x, y:b};
    return ret;
  } else {
    x.next = b;
    var ret = {x:a, y:x};
    return ret;
  }
}

/*@ quickSort :: forall A. (<m>+null)/m |-> list[A] => <o>+null/o |-> sList[{A | true}] */
function quickSort(x){
  if (typeof(x) == "null"){
    return null;
  }
  var piv = x.data;
  var xn  = x.next;
  var yz  = partition(piv, xn);
  var ls  = quickSort(yz.x);
  var gs  = quickSort(yz.y);
  x.next  = gs;
  var ret = append(piv, ls, gs);
  return ret;
}

