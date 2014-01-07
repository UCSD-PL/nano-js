/*@ foo :: forall <p :: (number) => Prop>.
             (number) => {number<p> | true} */
function foo(x) { return x; }

/*@ foo2 :: forall <p :: (number) => Prop, q :: (number) => Prop>.
             (number<p>) => {number<p, q> | true} */
function foo2(x) { return x; }
