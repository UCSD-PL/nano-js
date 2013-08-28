/*@ inc :: (ref l)/l |-> number => void/l |-> number */
function inc(x){
    var xv = !x;
    var res = xv + 1;
    x := res;
    return;
}

/*@ main :: () => void */
function main(){
    var a = ref (pos());
    var b = inc(a);
    assert (!b == !a+1);
}
