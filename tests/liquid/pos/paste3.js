/////////////////////////////////////////////////////////////////
// Paste Demo 3//////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

/*@ range :: (int, int) => list[int] */
function range(lo, hi) {
  var res = empty();
  if (lo < hi) {
    res = range(lo + 1, hi);
    res = push(lo, res);
  }
  return res;
}

/*@ reduce :: forall A B. (list[B], A, (A, B) => A) => A */
function reduce(xs, acc, f){
  if (!empty(xs)) {
    acc = f(acc, top(xs));
    acc = reduce(pop(xs), acc, f);
  }
  return acc;
}

/*@ minIndex :: (list[int]) => int */ 
function minIndex(a){
  function step(i, min){
    return a[i] < a[min] ? i : min;
  }
  var is = range(0, length(a));
  return reduce(is,0,step);
}

