/*@ nnull :: ({v:<l> | true})/l |-> { next:<l>+null } => void/same */
function nnull(p) {
    assert(typeof(p.next) != "null");
    return;
}
