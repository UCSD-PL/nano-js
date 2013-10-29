/*@ qualif NNull0(v:a, x:b): ((ttag(v) = "null") => (ttag(x) = "null")) */
/*@ qualif NNull0(v:a, x:b): ((ttag(v) != "null") => (ttag(x) != "null")) */
/* qualif NNull0(v:a, x:b): ((ttag(v) != "null") => (x = v)) */
/* qualif NNull2(v:a, x:a): (v = x) */
/* qualif NNullFFF(v:a, x:b): (((ttag v) = "null") => (0 = 1)) */
/* qualif NNullFFF(v:a, x:b): (((ttag v) != "null") => true) */

/* type cell exists! l |-> cell . {next: <l>+null } */

/*@ foo :: (<l>+null)/l |-> {} => {a:void | true}/l |-> {} */
function foo(x) {
    var z = null;

    if (typeof(x) != "null") {
        z = x;
    }

    if (typeof(x) == "null") {
        assert (typeof(z) == "null");
    } 

    return;
}
