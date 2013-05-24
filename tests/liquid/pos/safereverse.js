/*@ reverse :: forall A. (xs:list [A]) => {v:list [A] | (len v) = (len xs)} */
function reverse(xs){

  /*@ go :: (list [A], list[A]) => list [A] */ 
  function go(acc, ys){
    if (empty(ys)){
      return acc;
    }
    
    var y    = safehead(ys);
    var ys_  = safetail(ys);
    var acc_ = cons(y, acc);
    
    return go(acc_, ys_);
  }
  var b = nil();
  return go(b, xs);
}

