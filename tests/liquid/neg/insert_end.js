/*@ qualif Foo(v:a) : len(v) = 3 */

/*@ mkList  :: forall A. (A)/emp => <l>/l |-> ls:{list[A] | (len(v) = 1)}*/

/*@ insert_end :: forall A.
  (A, {x:<l> | true})/l |-> xs:list[A]
               => <r>/r |-> rs:{list[A] | len(v) = 3 } */
function insert_end(k, x) {
    var ret = mkList(k);

    if (typeof(x) != "null") {
        x.next = ret;
    }

    return x;
}
