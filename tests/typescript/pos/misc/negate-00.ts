/*@ negate :: ({xxx: number + boolean | true }) => 
    { ww: number + boolean | (ttag(ww) = ttag(xxx)) } */
function negate(x):any {
  if (typeof(x) == "number") {
    return 0 - x;
  } else {
    return !x;
  }
}
