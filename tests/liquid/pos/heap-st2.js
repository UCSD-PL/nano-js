/*@ foo :: ({x:<l> | (ttag x) = "reference"})/m |-> {n:{number|true}}
                                            * l |-> {a:null} =>
                                         void/m |-> {n:{number | v = 1}}
                                            * l |-> {a:{v:<m>+null | true}} */
function foo(x) {
    return;
}
