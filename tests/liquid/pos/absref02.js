/*@ type list[A] <p :: (A, A) => prop>
      exists! l |-> list[A<p (field me "data")>]<p> . me:{data:A, next:<l>+null} */

/*@ foo :: (l:<l>, {number | true})/l |-> x1:list[number]<{\h v -> h = 0}>
                            => void/l |-> x2:list[number]<{\h v -> h = 0}> */
function foo(l, k) {
  return;
}
