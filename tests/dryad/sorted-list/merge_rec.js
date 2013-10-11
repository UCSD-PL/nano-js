import "sorted-list.js";

/*@ merge :: (x1:?incList[A], x2:?incList[A]) => ?incList[A] */

/*@ merge :: (x1:?incList[A], x2:?incList[A]) => <?l>/l|-> {v:incList[A] | keys(v) = Set_cup(keys(x1,h), keys(x2,h))} */

function merge(x1, x2){
  if (x1 == null){
    return x2;
  }
  
  if (x2 == null){
    return x1;
  }
  
  var x1k = x1.data;
  var x2k = x2.data;
  
  if (x1k <= x2k){
    var y   = merge(x1.next, x2);
    x1.next = y;
    return x;       // DRYAD: return {data : x1.data, next : y};
  } else { 
    // x1k > x2k
    var y   = merge(x1, x2.next);
    x2.next = y;
    return x2;      // DRYAD: return {data : x2.data, next: y} ;
  }
}

// NOT IN DRYAD

/*@ split :: (x:list[A]) => {0: list[A], 1:list[A]} */

/*@ split :: (x:list[A]) => {0: <?l0>, 1:<?l1>}/l0 |-> list[A] * l1 |-> {v:list[A] | keys(x, h) = Set_cup(keys("0"), keys("1"))} */

function split(x){
  if (x == null){
    return [null, null];
  } 
  
  var xn = x.next;

  if (x.next == null){
    return [x, null];
  }

  var xnn = xn.next;
  var yz  = split(xnn);
  var y   = yz[0];
  var z   = yz[1];
  x.next  = y;
  xn.next = z;
  return   [x, xn];
}

// NOT IN DRYAD

/*@ sort :: (x:?list[A]) => {v: ?incList[A] | keys(v) = keys(x,h)} */
/*@ sort :: (x:?list[A]) => ?incList[A] */
function sort(x){
  if (x == null){
    return x;
  }
  var xn = x.next;
  if (xn == null){
    return x;
  }
  var yz = split(x);
  var ys = sort(yz[0]);
  var zs = sort(yz[1]);
  return merge(ys,zs);
}
