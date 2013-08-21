/*@ id :: forall A B. (x:<l>)/l |-> {a: A, b: B} => A/same */
function id(x) {
    return x.a;
}

/*@ mk :: (<l>,<m>)/l |-> number * m |-> number  => <l>/same */
function mk(x, y) {
  if (1) {
    return x;
  } else {
    return x;
  }
}
