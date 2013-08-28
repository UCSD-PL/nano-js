/*@ type nlist  list[number] */

// /*@ main :: (x:<l>, v:number)/l |-> nlist => <m>/m |-> nlist */
// function main(x, a) {
//     return { data: a , next: x };
// }

// /*@ append1 :: (x:nlist + null, number) => nlist */
// function append1(x, a) {
//   return { data: a , next: x };
// }

/*@ do_thing :: (<l>)/ l |-> foo[number] => <l>/l |-> { data:number, next:<m> + null } * m |-> foo[number] */
function do_thing(x) {
    unwind(x);
    return x;
}

