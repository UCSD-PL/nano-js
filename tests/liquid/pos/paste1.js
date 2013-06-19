/////////////////////////////////////////////////////////////////
// Paste Demo 1//////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////


/*@ loop :: (list[int], int, int) => int */
function loop(b, min, i){
  if (i < length(b)){
    if (b[i] < b[min])
      min = i;
    return loop(b, min, i+1)
  }
  return min;
}

/*@ minIndex :: (list[int]) => int */ 
function minIndex(a){
  return loop(a,0,0);
}

