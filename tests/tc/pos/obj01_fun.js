/*@ id :: forall A. (<l>)/l |-> A => <l>/same */
function id(x) {
  return x;
}

/*@ foo :: (<l>)/l |-> { a : number } => <l>/same */
function foo(z) {
  return id(z);
}
