/*@

type dlist[A,S,P] exists! l |-> ls:dlist[A, <l>, S] . me:{ data: A, next:<l>+null, prev:P }

with len(x) := (if (ttag(field(me,"next")) = "null") then 1 else (1 + len(ls)))

*/

/* remove :: (x:dlist[A, null], k:A)/h => {v:dlist[A, null]}/v |-> keys(v) = set_minus(keys(x,h), set_singleton(k)) */

/*@ remove :: forall A P.
  (x:<l>+null,k:{A | true})/l |-> ls:dlist[A,<l>,P] => <v>+null/v |-> vs:dlist[A,<v>,null] */
function remove(x, k){
  if (typeof(x) == "null"){
      return null;
  } else {
      var d = x.data;
      var r = remove(x.next,k);
      x.prev = null;
      x.next = r;

      if (d != k) {
          if (typeof(r) != "null") {
              r.prev = x;
          }
          return x;
      } else {
          if (typeof(r) != "null") {
              r.prev = null;
          }
          return r;
      }
  }
}
