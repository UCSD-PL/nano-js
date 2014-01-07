/*@ foo :: forall <p :: (number) => Prop>.
             (number<p>) => {number<p> | true} */
function foo(x) { return x; }

/*@ foo2 :: forall <p :: (number) => Prop, q :: (number) => Prop>.
             (number<p, q>) => {number<p> | true} */
function foo2(x) { return x; }
