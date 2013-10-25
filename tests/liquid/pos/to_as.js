/*@ to_as :: (a:{number|true},<l>)/l |-> xs:list[number] => void
                                  /l |-> ys:list[{v:number | v = a }] */

function to_as(a,x) {
    var xn = x.next;
    x.data = a;

    if (typeof(xn) != "null") {
        to_as(a,xn);
    }

    return;
}

/*@ qualif Eq3(v:int): v = 3 */
/*@ main :: (number,<l>)/l |-> ls:list[{number | v = 0}] => void/l |-> lso:list[{number | v = a}] */
function main(a,lst) {
    to_as(a,lst);
    var x = lst.data;
    assert (a == x);
    return;
}
    
