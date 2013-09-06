/*@ type nlist  list[number] */

/*@ main :: (x:<l>, a:number + boolean)/l |-> nlist => <m>/l |-> nlist * m |-> nlist */
function main(x, a) {

    return { data: a , next: x };

}


