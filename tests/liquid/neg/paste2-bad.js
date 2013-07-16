/////////////////////////////////////////////////////////////////
// Paste Demo 2//////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

/*@ loop :: (int, int, int, (int, int) => int) => int */
function loop(lo, hi, acc, body){
  if (lo < hi) {
    acc = body(lo, acc);
    return loop(lo + 1, hi, acc, body);
  }
  return acc;
}

/*@ minIndex :: (list[int]) => {v:int | true} */ 
function minIndex(a){
  /*@ step :: (int, int) => int */
  function step(i, min){
    if (a[i] < a[min]) 
      min = i;
    return min;
  }
  return loop(0, 1 + length(a), 0, step);
}


