/* find :: forall A. (k:A, <x> + null)/x |-> xs:list[A] => {v:boolean | ((Prop v) <=> (Set_elem k (keys xs)))}/same */
/*@ find :: forall A. (k:A, <x> + null)/x |-> xs:list[A] => {v:boolean | true}/same */
function find(k, x) {
    if (typeof(x) == "null") {
        return false;
    }

    var xd = x.data;
    // l |-> y:{ data:A, next:<m>+null } * m |-> z:list[A]
    if (xd == k) {
        return true;
    } else {
        var xn = x.next;
        var ret = find(k,xn);
        return ret;
    }
}
  
