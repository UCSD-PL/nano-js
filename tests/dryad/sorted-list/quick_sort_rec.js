//import "sorted-list.js";
/*@ qualif MinEq(v:a): (min(v) = min(ll) || v = mm) */
/*@ qualif AppKeys(v:a): (if (ttag(ls) = "null")
                             then (if (ttag(gs) = "null")
                                      then true
                                      else (keys(v) = keys(mm)))
                             else (if (ttag(gs) = "null")
                                      then (keys(v) = keys(ll))
                                      else (keys(v) = Set_cup(keys(ll),keys(mm))))) */

/*@  append :: forall A. (xk:A, ls:<l>+null, gs:<m>+null)/l |-> ll:sList[{A | v <  xk }]
                                                        * m |-> mm:sList[{A | v >= xk }]
                                   => {v:<k>+null | ((ttag(v) = "null") <=>
                                                    ((ttag(ls) = "null") && (ttag(gs) = "null")))}
                                      /k |-> kk:{sList[A] | (((min(v) = min(ll)) || (v = mm))
                                                         && (if (ttag(ls) = "null")
                                                                then (if (ttag(gs) = "null")
                                                                         then true
                                                                         else (keys(v) = keys(mm)))
                                                                else (if (ttag(gs) = "null")
                                                                         then (keys(v) = keys(ll))
                                                                         else (keys(v) = Set_cup(keys(ll),keys(mm))))))} */
function append(xk, ls, gs) {
  if (typeof(ls) == "null") {
    return gs;
  }

  var n = ls.next;
  if (typeof(n) == "null") {
    ls.next = gs;
  } else {
    n = append(xk, n, gs);
    ls.next = n;
  }
  return ls;
}

/*@ partition :: forall A.
   (piv:A, x:<x>+null)/x |-> xs:list[A] => <r>/a |-> as:list[{A | v < piv}]
                                             * b |-> bs:list[{A | v >= piv}]
                                             * r |-> p:{v:{x:<a>+null, y:<b>+null} |
                                                        ((((ttag(field(p,"x")) = "null") && (ttag(field(p,"y")) = "null"))
                                                            <=> (ttag(x) = "null"))
                                                        &&  (if (ttag(field(p,"x")) = "null")
                                                                then (if (ttag(field(p,"y")) = "null")
                                                                         then true
                                                                         else (keys(xs) = keys(bs)))
                                                                else (if (ttag(field(p,"y")) = "null")
                                                                         then (keys(xs) = keys(as))
                                                                         else (keys(xs) = Set_cup(keys(as),keys(bs)))))) }
                                             */

/*@ nullList :: forall A. () => {v:<l>+null | (ttag(v) = "null")}/l |-> list[A] */
function partition(piv, x){
  if (typeof(x) == "null") {
      var x = nullList();
      var y = nullList();
      var ret = {};
      ret.x = x;
      ret.y = y;
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
      (x:<m>+null)/m |-> ms:list[A] => {v:<o>+null | ((ttag(v) = "null") <=> (ttag(x) = "null"))}
                                       /o |-> {sList[A] | ((ttag(lqreturn) != "null") => (keys(v) = keys(ms)))} */
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
  var ret = append(piv, ls, x);
  return ret;
}

