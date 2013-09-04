/*@ inc :: (<l>)/l |-> {n:number} => void/l |-> {n:number} */
function inc(x){
    x.n = x.n + 1;
    return;
}

/*@ main :: () => void */
function main(){
    var a = ref (pos());
    var b = inc(a);
    assert (!b == !a+1);
}
