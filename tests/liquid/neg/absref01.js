/*@ foo :: forall <p :: (number) => prop> .
             (number<p>) => number */

/*@ foo2 :: ({number | v > 0}) => {number | v > 0} */
function foo2(z) {
  return foo(z);
}
