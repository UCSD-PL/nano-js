//import "sorted-list.js";

// NOT IN DRYAD

/* append :: (xk:A, ls: incList[{v:A | v <= xk}], gs: incList[{v:A | v > xk}]) => incList[A]*/  
/*@
  append :: (xk:{number | true}, ls:<l>+null, gs:<g>+null)/l |-> list[number] * g |-> list[number] => <r>+null/r |-> list[number]
*/
function append(xk, ls, gs){
    if (typeof(ls) == "null"){
        return gs;
    }
    var n = ls.next;
    ls.next = append(xk, n, gs);
    return ls;
}

/*@ partition :: (piv:{number | true}, x:<x>+null)/x |-> list[number] => <r>/r |-> {x:<a>+null, y:<b>+null} * a |-> list[number] * b |-> list[number] */  
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
  if (xd <= piv){
    x.next = a;
    var ret = {x:x, y:b};
    return ret;
  } else {
    var ret = {x:a, y:x};
    return ret;
  }
}

/*@ quickSort :: (<m>+null)/m |-> list[{number | true}] => <o>+null/o |-> list[number] */
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

