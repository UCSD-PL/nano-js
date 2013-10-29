/*@ mkList :: forall A.
      (k:A)/emp => <l>/l |-> {list[A] | ((len(v) = 1)
                                      && (keys(v) = Set_sng(k))) }
 */
function mkList(k) {
    var l = { data:k, next:null };
    return l;
}
