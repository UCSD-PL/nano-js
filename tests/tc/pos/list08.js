/*@ type nlist  list[number] */ 

/*@ foo :: (x:<l> + number)/l |-> nlist => <m>/m |-> nlist */
function foo(x) {
  var l = { data: 5, next: x };
  return l;
}
