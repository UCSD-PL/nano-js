// import "singly-linked-list.js"


/*@ insert :: forall A. (x:<l>+null, k:A)/l |-> list[A] => <m>/m |-> {v:list[A]| keys(v) = set_cup(keys(x), set_singleton(k))} */
function insert(x, k){
    var y = {};
    y.data = k;
    y.next = x;
    return y;
}
