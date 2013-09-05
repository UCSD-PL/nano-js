/*@ foo :: (<l>, <m>)/l |-> {a:number} * m |-> {a:number} => number/same */

/*@ bar :: ()/emp => void/l |-> {a:number} */
function bar () {
    x = {a:3};
    foo(x,x);
    return;
}
