/*@ id :: forall A. (A) => A */
function id(x){
  return x;
}

/*@ foo :: /\ (number)  => {number  | true} 
           /\ (boolean) => {boolean | true} 
           /\ (string)  => {string  | true}
 */
function foo(y){
  var z = id(y);
  return z;
}
