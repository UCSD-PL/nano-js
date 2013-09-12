/*@ main :: (x:<l>, v:number)/l |-> list[number] => <m>/m |-> list[number] */
function main(x, a) {
    z = { data: a, next: x };
    return z;
}
