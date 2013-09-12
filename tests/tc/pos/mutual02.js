
/*@ type e  {  next : e } */

/*@ type a  {  next : b } */
/*@ type b  {  next : c } */
/*@ type c  {  next : a } */


/*@ foo :: (x: <l>)/l |-> a => <l>/l |-> e */
function foo(x) {
    return x;
}

