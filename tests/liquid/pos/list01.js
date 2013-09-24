/*@ main :: (x:<z>,a:number)/z |-> inflist[{number|true}] => <m>/m |-> inflist[{number|true}] */
function main(x,a) {
    z = { data: a, next: x };
    return z;
}
