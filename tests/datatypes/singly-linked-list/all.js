/*@ include singly-linked-list.js */
/*@ qualif EqL(v:a): lenp(v,ks) = lenp(i,is) + lenp(j,js) */
/*@ qualif EqK(v:a): keysp(v,ks) = Set_cup(keysp(i,is),keysp(j,js)) */

/*@ append :: (x1:<l>+null, x2:<m>+null)/l |-> x1s:list[number] * m |-> x2s:list[number]
               => {v:<k>+null | ((lenp(v,ks) = lenp(x1,x1s) + lenp(x2,x2s))
                              && (keysp(v,ks) = keysp(x1,x1s) ∪ keysp(x2,x2s)))}
                  /k |-> ks:list[number]
*/
function append(x1, x2){
  if (x1 != null){
      var n = x1.next;
      x1.next = append(n, x2);
      return x1;
  } else {
      return x2;
  } 
}

/*@
  copy ::
    (x:<l>+null)/l |-> xs:list[number]
      => {v:<m>+null | ((lenp(v,ms) = lenp(x,xs))
                     && (keysp(v,ms) = keysp(x,xs)))}
        /l |-> xss:list[number] * m |-> ms:list[number]
*/
function copy(x){
  if (x == null){
    var ret = null;
    return ret;
  }
  var u  = copy(x.next);
  var t  = {data: x.data, next: u};
  return t;
}


/*@
  remove ::
    (x:<l>+null, k:number)/l |-> xs:list[number]
     => {v:<m>+null | (keysp(v,ms) = Set_dif(keysp(x,xs),Set_sng(k)))}
        /m |-> ms:list[number]
*/
function remove(x, k){
  if (x != null) {
    var xn = x.next;
    var t = remove(xn, k);
    x.next = t;
    var d = x.data;
    if (d == k) {
      return t;
    } else {
      return x;
    }
  }

  return null;
}

/*@ find :: forall A. 
  (x:<l>+null,k:A)/l |-> xs:list[A] => 
  {v:boolean | (Prop(v) <=> Set_mem(k, keysp(x,y))) }
  /l |-> y:list[A] */
function find(x, k){
  if (x != null){ 
    var xk = x.data; 
    if (xk == k) {
      return true;
    } else {
      r = find(x.next, k);
      return r;
    }
  }
  return false;
}

/*@ insertBack :: 
  (x:<l>+null, k:number)/l |-> xs:list[number]
    => {v:<m> | ((lenp(v,ys) = 1 + lenp(x,xs)) && (keysp(v,ys) = keysp(x,xs) ∪1 k))}
      /m |-> ys:list[number]
*/
function insertBack(x, k){
  if (x != null){
    var n = x.next;
    var t = insertBack(n, k);
    x.next = t;
    return x;
  }
  var y  = {data:k, next:x};
  return y;
}

/*@ insert ::
  (x:<l>+null, k:number)/l |-> xs:list[number] =>
                   {v:<m> | ((lenp(v,ys) = lenp(x,xs) + 1)
                          && (keysp(v,ys) = keysp(x,xs) ∪1 k)) }
                   /m |-> ys:list[number] */
function insert(x, k) {
  var y = {};
  y.data = k;
  y.next = x;
  return y;
}

/*@ reverseLoop :: 
  (i:<i>+null, j:<j>+null)/i |-> is:list[number] * j |-> js:list[number]
    => <k>+null/k |-> ks:list[number]
*/
function reverseLoop(i, j){
  if (i != null) {
    var temp = i.next;
    i.next   = j;
    var a    = i;
    var r    = reverseLoop(temp, a);
    return r;
  } else {
    return j;
  }
}

/*@ reverse ::
  (x:<x>)/x |-> xs:list[number] => {v:<y>+null | ((lenp(v,ys) = lenp(x,xs))
                                               && (keysp(v,ys) = keysp(x,xs))) }
                              /y |-> ys:list[number]*/
function reverse(x){
  var r = reverseLoop(x,null);
  return r;
}

