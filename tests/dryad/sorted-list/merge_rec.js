/*@ merge :: forall A. (x1:<a>+null, x2:<b>+null)/a |-> x1s:sList[A] * b |-> x2s:sList[A]
                                => {v:<m>+null | ((ttag(v) = "null") <=> ((ttag(x1) = "null") && (ttag(x2) = "null"))) }
                                  /m |-> ms:{sList[A] | (if (ttag(x1) != "null") then
                                                            (if (ttag(x2) != "null") then
                                                                (keys(v) = Set_cup(keys(x1s), keys(x2s)))
                                                            else
                                                                (keys(v) = keys(x1s)))
                                                        else
                                                            (if (ttag(x2) != "null") then
                                                                (keys(v) = keys(x2s))
                                                            else
                                                                true)) }

*/
function merge(x1, x2){
  if (typeof(x1) == "null"){
    return x2;
  }
  
 if (typeof(x2) == "null"){
   return x1;
 }
  var x1k = x1.data;
  var x2k = x2.data;
  
  if (cmp(x1k,x2k)){
    var n   = x1.next;
    var y   = merge(n, x2);
    x1.next = y;
    return x1;       // DRYAD: return {data : x1.data, next : y};
  } else { 
    //x1k > x2k
    var y   = merge(x1, x2.next);
    x2.next = y;
    return x2;      // DRYAD: return {data : x2.data, next: y} ;
  }
}

/*@ split :: forall A. (x:<l>+null)/l |-> ls:list[A] =>
                                <r>/r |-> r:{x:{v:<x>+null | ((ttag(v) = "null") <=> (ttag(x) = "null"))},
                                             y:{v:<y>+null | ((ttag(v) != "null") <=> ((ttag(x) != "null") && (len(ls) > 1)))}}
                                  * x |-> xs:{list[A] | ((ttag(field(r, "y")) = "null") => (keys(v) = keys(ls)))}
                                  * y |-> ys:{list[A] | (if (ttag(field(r, "x")) != "null") then
                                                          (if (ttag(field(r, "y")) != "null") then
                                                              (keys(ls) = Set_cup(keys(xs), keys(v)))
                                                          else
                                                              (keys(ls) = keys(xs)))
                                                      else
                                                          (if (ttag(field(r, "y")) != "null") then
                                                              (keys(ls) = keys(ys))
                                                          else
                                                              true)) }                                                       */
function split(x){
  if (typeof(x) == "null"){
    r = {x:null, y:null};
    return r;
  } 
  
  var xn = x.next;

  if (typeof(xn) == "null"){
    r = {x:x, y:null};
    return r;
  } else {
    var xnn = xn.next;
    var yz  = split(xnn);
    var y   = yz.x;
    var z   = yz.y;
    x.next  = y;
    xn.next = z;
    r = {x:x, y:xn};
    return r;
  }
}

/*@ sortList :: forall A. (x:<j>+null)/j |-> js:list[A] => {v:<k>+null | ((ttag(v) = "null") <=> (ttag(x) = "null"))}
                                      /k |-> ks:{sList[A] | ((ttag(x) != "null") => (keys(v) = keys(js)))}            */
function sortList(x) {
  if (typeof(x) == "null"){
    return null;
  }
  var xn = x.next;
  if (typeof(xn) == "null") {
    return x;
  }
  var yz = split(x);
  var y = yz.x;
  var z = yz.y;
  var ys = sortList(y);
  var zs = sortList(z);
  var ret = merge(ys,zs);
  if (typeof(ys) != "null") {
    if (typeof(zs) != "null") {
      return ret;
    } else {
      return ret;
    }
  } else {
    if (typeof(zs) != "null") {
      return ret;
    } else {
      return ret;
    }
  }
}
