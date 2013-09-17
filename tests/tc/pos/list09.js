/*@ cond_append  :: (<l>,number)/l |-> list[number] => <l>/l |-> list[number] */
function cond_append(l,x) {
    l.next = { data:x, next: null };
    return l;
}
