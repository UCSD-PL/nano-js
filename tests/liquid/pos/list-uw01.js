/*@ inspect :: (<l>)/ l |-> list[{number | true}] => void/same */
function inspect(x) {
    var xn = x.next;
    if (typeof (xn) == "reference") {
        return;
    } else {
        return;
    }
}
