/*@ nnull :: ({v:<l> | true})/l |-> { next:<l>+null } => void/same */
function nnull(p) {
    if (typeof(p.next) == "null") {
        assert(typeof (p.next) == "null");
    }

    return;
}
