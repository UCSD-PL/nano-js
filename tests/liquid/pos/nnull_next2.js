/*@ qualif NNull0(v:a, x:b): ((ttag(v) = "null") => (ttag(x) = "null")) */
/*@ qualif NNull0(v:a, x:b): ((ttag(v) != "null") => (ttag(x) != "null")) */

/*@ type cell[A] exists! l |-> cell[A] . me:{data:A, next: <l>+null } */
/*@ foo :: (k:number, x:<l>+null)/l |-> cs:cell[number] => {a:<k> | true}/k |-> ds:cell[number] */
function foo(k, x) {
    var z = { data: k, next: null};

    if (typeof(x) != "null") {
        z.next = x;
    }

    if (typeof(x) == "null") {
        var y = z.next;
        assert (typeof(y) == "null");
        return z;
    } 

    return z;
}
