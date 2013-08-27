/*@ getNum ::  (x:<l>)/l |-> { } => number/same */
function getNum(x) {

  if (x && x.a && typeof(x.a) == "number")
    return x.a;
  
  return -1;

}

