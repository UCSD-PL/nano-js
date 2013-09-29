/*@ main :: (a:number)/emp => <m>/m |-> list[{number|true}] */
function main(a) {
    z = { data: a, next: null };
    return z;
}
