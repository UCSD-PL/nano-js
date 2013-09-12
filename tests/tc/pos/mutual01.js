
/*@ type a  {  next : b } */
/*@ type b  {  next : c } */
/*@ type c  {  next : a } */


/*@ foo :: (x: <l>)/l |-> a => <l>/l |-> c */
function foo(x) {
    return x;
}

