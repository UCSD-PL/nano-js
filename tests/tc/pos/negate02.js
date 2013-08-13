/*@ negate :: (number) => number */
function negate(x) {

  //Revert when strings are supported   
  if (typeof(x) == "number") {
      return 0-x;
  }
  else {
    return !x;
  }
  
}

/*@ main :: (number) => void */ 
function main(x) {

  negate(x);

}
