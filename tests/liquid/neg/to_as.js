/*@ to_as :: (a:number,<l>)/l |-> list[number] => void
                           /l |-> list[{v:number | v = a }] */

function to_as(a,x) {
    var xn = x.next;
    x.data = a;
    if (typeof(xn) != "null") {
        // to_as(a,xn);
    }

    return;
}
