/*@ mkList :: (a:number)/emp => <l>/l |-> l:list[{number | v = a}] */
function mkList(a) {
    var lst = { data:a, next:null };
    return lst;
}

/*@ consList :: (a:number, l:<l>+null)/l |-> xs:list[{number | v < a}] => <k>/k |-> ys:list[{number | v <= a}] */
function consList(a, l) {
    var lst = { data:a, next:l };
    return lst;
}

