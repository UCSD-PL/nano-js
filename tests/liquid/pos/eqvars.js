/*@ foo :: ({number | true}, {number | true}) => void */
function foo(x,y) {
    x = y;
    assert(x == y);
}
