
/*@ foo :: (x:<l>)/l |-> {a:{number | v = 3}, *:boolean} => number/same */
function foo (x) {
  return x.a;
}
