/*@ include doubly-linked-list.js */

/*@ remove :: forall A P.
  (x:<l>+null,k:{A | true})/l |-> ls:dlist[A,<l>,P] => <v>+null/v |-> vs:dlist[A,<v>,null] */
function remove(x, k){
  if (x == null){
      return null;
  } else {
      var d = x.data;
      var r = remove(x.next,k);
      x.prev = null;
      x.next = r;

      if (d != k) {
          if (r != null) {
              r.prev = x;
          }
          return x;
      } else {
          if (r != null) {
              r.prev = null;
          }
          return r;
      }
  }
}
