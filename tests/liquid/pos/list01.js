/*
type inflist[A] exists! l |-> tl:list[A] . r:{ data : A, next : <l> }
*/
/*@ main :: (x:<z>,a:number)/z |-> inflist[{v:number|true}] => <m>/m |-> inflist[{v:number|true}] */
function main(x,a) {
    z = { data: a, next: x };
    return z;
}
