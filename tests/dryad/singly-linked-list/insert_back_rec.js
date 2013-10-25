//import "singly-linked-list.js"

/*@ qualif LenEq (v:a, x:b): len(v) = len(x) */

/* insert :: (x:?list[A], k:A) => {v:list[A]| keys(v) = set_cup(keys(x), set_singleton(k))} */
/* insert :: (x:?list[A], k:A)/h => {v:list[A]}/ v |-> keys(v) = set_cup(keys(x,h), set_singleton(k)) */

/* insert :: forall A. (x:<l>+null, k:A)/l |-> list[A] => <l>/l |-> {v:list[A]| keys(v) = set_cup(keys(x), set_singleton(k))} */

/*@ insert :: forall A. (x:<l>+null, k:A)/l |-> ls:{list[A] | (((ttag x) = "null") => (len v) = 0)} => <r>/r |-> out:{v:list[A] | len(v) = len(ls) + 1} */
function insert(x, k){
  if (typeof(x) != "null"){
      var n = x.next;
      var t = insert(n, k);
      x.next = t;
      return x;
  } else {
      var y  = {}; // {data : k, next : null };
      y.data = k;
      y.next = null;
      return y;
  }
}
