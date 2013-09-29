/*@ foo :: (a:number) => {number | v = a} */

/*@ bar :: (b:number) => {number | v = b} */
function bar(b) {
    var x = foo(b);
    return x;
}
    
