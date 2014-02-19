/*@ foo :: forall <p :: (number) => prop>.
             (x:number<p>)/emp => {v:number<p> | true}/emp */
// function foo(x) { return x; }

/*@ foo2 :: forall <p :: (number) => prop, q :: (number) => prop>.
             (x:number<p>) => number<p> */
function foo2(x) { return x; }
