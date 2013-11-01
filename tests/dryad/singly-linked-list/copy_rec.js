//import "singly-linked-list.js"

/*@ copy :: forall A. (x:<l>+null)/l |-> ls:list[A] => {v:<m>+null | ((ttag(x) != "null") <=> (ttag(v) != "null"))}
                                  /l |-> nls:{list[A] | (keys(v) = keys(ls) && len(v) = len(ls)) }
                                 * m |-> {list[A] | (len(v) = len(ls) && keys(v) = keys(ls))} */
function copy(x){
  if (typeof(x) == "null"){
    return null;
  } else {
    var u  = copy(x.next);
    var t  = {data: x.data, next : u};
    return t;
  } 
}

