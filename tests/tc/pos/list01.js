/*@ type nlist  list[number] */

/*@ main :: (x:<l>, v:number)/l |-> foo[] => <m>/m |-> foo[] */
function main(x, a) {
    z = { data: a, next: x };
    wind(z, foo);
    return z;
}

/*@ append1 :: (x:nlist + null, number) => nlist */
// function append1(x, a) {
//   return { data: a , next: x };
// }

/*@ do_thing :: (<l>)/l |-> { data:number, next:<m> + null }
                     * m |-> foo[]
                => <l>/l |-> foo[] */
// function do_thing(x) {
//     wind(x,foo);
//     return x;
// }

/*@ mkFoo :: (d:number)/emp => <l>/l |-> foo[] */
// function mkFoo(d) {
//     k = null;
//     m = { data:d, next:k };
//     l = { data:d, next:m};
//     wind(m,foo);
//     wind(l,foo);
//     return m;
// }

