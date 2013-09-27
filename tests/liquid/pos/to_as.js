/*@ to_as :: (a:{number|true},<l>)/l |-> list[number] => void
                                  /l |-> list[{v:number | v = a }] */

function to_as(a,x) {
    var xn = x.next;
    x.data = a;

    if (typeof(xn) != "null") {
        to_as(a,xn);
    }

    return;
}

/*@ main :: (number,<l>)/l |-> list[{number | v = 0}] => void/l |-> list[{number | v = 3}] */
function main(a,lst) {
    to_as(3,lst);
    var x = lst.data;
    assert (x == 3);
    return;
}
    
