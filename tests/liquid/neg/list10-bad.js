/*@ hop :: (list [{v:number| 0 < v}] + null) => list [{v:number| 10 < v}] */
function hop(xs){
  if (empty(xs)) 
    return { data: 15, next: null };
  else 
    return xs;
  
}

