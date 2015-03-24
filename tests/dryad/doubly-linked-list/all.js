/*@ include doubly-linked-list.js */

/*@ append :: forall P.
  (x1:<r>+null, x2:<m>+null)/r |-> x1s:dlist[number,<r>,P]
                           * m |-> x2s:dlist[number,<m>,null]
      => {v:<k>+null | ((dlenp(v,ks) = dlenp(x1,x1s) + dlenp(x2,x2s)) 
                     && (dkeysp(v,ks)= Set_cup(dkeysp(x1,x1s),dkeysp(x2,x2s)))
                     && (v = null <=> (x1 = null && x2 = null)))}
        /k |-> ks:dlist[number,<k>,null]
*/
function append(x1, x2) {
  if (x1 == null)
    return x2;

  x1.prev = null;
  
  if (x2 == null)
    return x1;

  var n = x1.next;
  var t = append(n, x2);

  x1.next = t;
  x1.prev = null;
  t.prev = x1;

  return x1;
}

/* qualif LLen(v:dlist[a]):
      (keys(v) = (Set_cup(Set_sng(field(y, "data")),
                          dkeysp(field(y, "next"), ys)))) */

/*@ remove :: forall P.
  (x:<l>+null,k:number)/l |-> ls:dlist[number,<l>,P]
    => r:{v:<v>+null | dkeysp(v,vs) = Set_dif(dkeysp(x,ls),Set_sng(k))}
       /v |-> vs:dlist[number,<v>,null] */
function remove(x, k){
  if (x == null){
    return null;
  } else {
    var d = x.data;
    var r = remove(x.next,k);
    x.prev = null;
    x.next = r;
    
    if (d != k) {
      if (r != null) {
        r.prev = x;
        return x;
      } else {
        return x;
      }
    } else {
      delete(x);
      if (r != null) {
        r.prev = null;
        return r;
      } else {
        return r;
      }
    }
  }
}

/*@
  insert :: forall P.
    (x:<l>+null, k:number)/l |-> xs:dlist[number,<l>,P]
       => r:{v:<k> | ((dlenp(v,ks) = 1+dlenp(x,xs))
                   && (dkeysp(v,ks) = dkeysp(x,xs) ∪1 k)) }
         /k |-> ks:dlist[number,<k>,null]
*/
function insert(x, k){
  if (x != null){
    var y  = x.next;
    var t  = insert(y, k);
    x.next = t;
    t.prev = x;
    x.prev = null;
    return x;
  } else {
    var y  = {}; // {data : k, next : null, prev: null};
    y.data = k;
    y.next = null;
    y.prev = null;
    return y;
  }
}

/*@ qualif EqMeas(v:a, vs:b): ((dlenp(v,vs) = dlenp(x,xs))
                              && (dkeysp(v,vs) = dkeysp(x,xs))) */
/*@
  insertFront ::
    (x:<x>+null, k:number)/x |-> xs:dlist[number,<x>,null]
       => r:{v:<j> | ((dlenp(v,js) = 1 + dlenp(x,xs))
                  && (dkeysp(v,js) = dkeysp(x,xs) ∪1 k))}
         /j |-> js:dlist[number,<j>,null]
*/
function insertFront(x, k){
  var y  = {data:k, next:x, prev:null};

  if (x != null) {
    x.prev = y;
  }

  return y;
}


/*@ qualif EqLen(v:a, x:b): (len(v) = len(x)) */
/*@ qualif NNull(v:a, p:b): ((p = null) <=> (v = null)) */
/*@ qualif NNull(v:a): (v = null) */

/*@ delete_at_middle :: 
      (q:<q>)/p |-> pp:{ data:number, next:{v:<q>+null | ((v = null) <=> (field(qq,"prev") = null))}, prev:null }
            * q |-> qq:{ data:number, next:<r>+null, prev:{v:<p>+null | ((v = null) <=> (field(pp,"next") = null)) }}
            * r |-> rr:dlist[number,<r>,{v:<q>+null | ((v = null) <=> (field(qq,"next") = null))}]
                              => <k>+null/p |-> ps:{ data:number, next:<k>+null, prev:null }
                                        * k |-> rs:dlist[number,<k>,<p>+null]
 */
function delete_at_middle (q) {
  var p = q.prev;
  var r = q.next;

  q.prev = null;
  q.next = null;

  if (p != null) {
    p.next = r;
  }
  
  if (r != null) {
    r.prev = p;
    return r;
  } else {
    return r;
  }

}

/*@ qualif Same(v:a,vs:b): (dkeysp(v,vs) = dkeysp(t,ts)
                          && dlenp(v,vs) = dlenp(t,ts)) */
/*@ qualif Field(v:x): v = field(us, "data") */


/*@ insert_at_middle ::
      (u:<a>+null, k:number, t:<b>+null)/a |-> us:{ data:number, next:<b>+null, prev:null }
                                       * b |-> ts:dlist[number,<b>,null]
                             => {v:<r>+null | ((u != null => (dlenp(v,rs) = 2 + dlenp(t,ts)))
                                             &&(u != null => (dkeysp(v,rs) = Set_cup(Set_sng(field(us,"data")),Set_cup(Set_sng(k),dkeysp(t,ts))))))}
                                /r |-> rs:dlist[number,<r>,null]
*/
function insert_at_middle (u, k, t) {
  ret = { data:k, next:t, prev:u };

  if (t != null) {
    t.prev = ret;
  }

  if (u != null) {
    u.next = ret;
    return u;
  } else {
    return ret;
  }
}
