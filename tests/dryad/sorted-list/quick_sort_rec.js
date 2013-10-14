import "sorted-list.js";

// NOT IN DRYAD

/*@ append :: (xk:A, ls: incList[{v:A | v <= xk}], gs: incList[{v:A | v > xk}]) => incList[A]*/  
function append(xk, ls, gs){
  if (ls == null){
    return gs;
  }
  ls.next = append(xk, ls.next, gs);
  return ls;
}

/*@ partition :: (piv:A, x: list[A]) => {0: list[A], 1: list[A]} */  
function partition(piv, x){
  if (x == null){
    return [null, null];
  }
  var yz = partition(x.next);
  if (x.data <= piv){
    x.next = yz[0];
    return [x, yz[1]];
  } else {
    x.next = yz[1];
    return [yz[0], x];
  }
}

/*@ quickSort :: (x: ?list[A]) => ?incList[A]  */  
function quickSort(x){
  if (x == null){
    return null;
  }
  var piv = x.data;
  var yz  = partition(piv, x.next);
  var ls  = quickSort(yz[0]);
  var gs  = quickSort(yz[1]);
  x.next  = gs;
  return append(piv, ls, x);
}

