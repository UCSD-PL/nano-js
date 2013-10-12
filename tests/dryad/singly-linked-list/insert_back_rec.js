import "singly-linked-list.js"

/* insert :: (x:?list[A], k:A) => {v:list[A]| keys(v) = set_cup(keys(x), set_singleton(k))} */
/* insert :: (x:?list[A], k:A)/h => {v:list[A]}/ v |-> keys(v) = set_cup(keys(x,h), set_singleton(k)) */

/*@ insert :: forall A. (x:<l>+null, k:A)/l |-> list[A] => <l>/l |-> {v:list[A]| keys(v) = set_cup(keys(x), set_singleton(k))} */
function insert(x, k){
  if (typeof(x) != "null"){
      x.next = insert(x.next, k);
      return x;
  } else {
      var y  = {}; // {data : k, next : null };
      y.data = k;
      y.next = null;
      return y;
  }
}
