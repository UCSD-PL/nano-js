/*@ sum :: (x:<l>)/l |-> list[number] => number */
function sum(l) {
    
  var s = 0;
  
  if (l != null) {
    return l.data;
  }

  return 0;
}
