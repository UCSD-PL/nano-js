
/*@ safeNull :: forall A . (x:<l> + null, def: <l>)/l |-> list[A] => <l>/same */
function safeNull(x, def) {

  if (empty(x)) 
    return def;
  else 
    return x;

}
