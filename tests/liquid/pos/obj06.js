
/*@ foo :: (<l>)/l |-> { a: { number | v = 3 }, *: boolean } => boolean/same */
function foo (x) {
  return x.b;
}
