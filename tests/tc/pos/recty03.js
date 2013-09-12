/*@ sum :: (x:<l>)/l |-> list[number] => number/l |-> list[number] */
function sum(l) {
    
  var s = 0;
  
  if (l != null) {
    var x = l.data;
    return x; //l.data;
  }

  return 0;
}
