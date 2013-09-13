/*@ foo :: (x:<l> + number)/l |-> list[number] => <m>/m |-> list[number] */
function foo(x) {
  var l = { data: 5, next: x };
  return l;
}
