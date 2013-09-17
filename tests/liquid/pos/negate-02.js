
/*@ negate :: (x: {number | v > 0} + boolean) =>  { v: number | v > 0 } + boolean */

function negate(x) {
  if (typeof(x) == "number") {
    return x;
  } 
  return 1;
  
}

