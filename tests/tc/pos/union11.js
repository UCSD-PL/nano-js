/*@ id :: forall A . (<l>,<m>)/l |-> A * m |-> A => <m>/same */
function id(a,b) {
  return b;
}

/*@ foo :: () => <l>/l |-> {a:number} */
function foo() {
  return id({a:2},{a:1});
}

