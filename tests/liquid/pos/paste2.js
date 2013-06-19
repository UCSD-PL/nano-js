/////////////////////////////////////////////////////////////////
// Paste Demo 2//////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

//@ loop :: (int,int,int,(int,int)=>int)=>int
function loop(lo, hi, acc, body){
  if (lo < hi) {
    acc = body(lo, acc);
    return loop(lo + 1, hi, acc, body);
  }
  return acc;
}

/*@ minIndex :: (list[int]) => int */ 
function minIndex(a){
  function step(i, min){
    return a[i] < a[min] ? i : min;
  }
  return loop(0, length(a), 0, step);
}


