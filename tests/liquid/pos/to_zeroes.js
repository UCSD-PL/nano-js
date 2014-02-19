/*@
type list[A] exists! l |-> tl:list[A] . r:{ data : A, next : <l> + null }
*/
/*@ to_zeroes :: (<l>)/l |-> xs:list[{v:number|v = 1}] => void/l |-> ys:list[{v:number | v = 0 }] */
function to_zeroes(x) {
    var n = x.next;
    x.data = 0;

    if (n != null) {
        to_zeroes(n);
    } else {
    }

    return;
}
    
// /* to_zeroes2 :: (<l>)/ l |-> xs:list[{number|v = 1}] => void/l |-> ys:list[{number | v = 0 }] */
// function to_zeroes2(x) {
//     x.next = null;
//     x.data = 1;

//     return;
// }
