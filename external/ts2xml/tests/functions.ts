/**
 *  Functions and variables related to numeric calculus.
 */
module Numerics {

	export var PI :number = Math.PI;

	function add(a :number, b :number) : number {
		return a + b;
	}

	function gcd(a :number, b :number) : number {
		var c : number;
		while ( a != 0 ) {
			c = a; 
			a = b%a;  
			b = c;
		}
		return b;
	}

	function fact(n :number) : number {
		if (n == 1) return 1;
		return fact(n-1)*n;
	}

	//Recursive definition of Fibonacci
	function fibonacci_rec(n : number) : number {
		if (n == 0 || n == 1) return 1;
		return fibonacci_rec(n-1) + fibonacci_rec(n-2);
	}

	//Iterative definition of Fibonacci
	function fibonacci_iter(n :number) : number{
		if (n == 0 || n == 1) return 1;
		var b : number = 1;
		var c : number = 1;
		var a : number = b + c;
		while (n > 0){
			b = a;
			c = b;
			a = b +c;
			n--;
		}
		return a;
	}
}


/**
 * Module with functions regarding lists
 */
module MyLists{

	//Sum eletements of a list (operator + has to be defined for the type contained)
	function sum_list(l : any[]) : number {
		var s :number = 0;
		for (var i :number = 0; i < l.length ; i++){
			s += l[i];
		}
		return s;
	}

	export function contains(l :any[], o : any) : boolean {
		for (var i : number = 0 ; i < l.length ; i++){
			if (l[i] == o){
				return true;
			}
		}
		return false;
	}

	//Remove elements of l not verifying the predicate f.
	function remove(f :(v:number) => boolean, l :any[]) : any[]{
		for (var i :number = 0 ; i < l.length ; i++){
			if(!f(l[i])){
				l.splice(i,1);
			}
		}
		return l;
	}

	//Apply f to all the elements of a list
	function mapcar(f :(v:number) => boolean, l :any[]) : any[]{
		var result : any[] = [];
		for (var i :number = 0 ; i < l.length ; i++){
			result.push(f(l[i]));
		}
		return result;
	}

	//Quick sort
	function qsort(l : any[]) :any[] {
		if (l.length == 0){
			return l;
		}
		var p : number = l[0];
	    var left :any[] = []; 
	    var right :any[] = [];
	    l.shift(); //Remove the head
	    //for(var i in l){   //No type annotation allowed in this syntactic sugar
	    for (var i :number = 0; i < l.length ; i++){
	    	(l[i]>p) ? right.push(l[i]) : left.push(l[i]);
	    }
	    right = qsort(right);
	    left  = qsort(left);
	    left.push(p);
	    return left.concat(right);;
	}

}

//Bynary tree. Only leaves have content (not in order!)
interface BTree {
	//Sum the elements of all the leaves
	sum() : number;
	//Height
	height() : number;
}

class Leaf implements BTree{
	public value : number;
	public sum() : number {return this.value;}
	public height() : number {return 0;}
}

class BNode implements BTree{
	lt : BTree;
	rt : BTree;

	public addLeft(t : BTree) : void{
		this.lt = t;
	}

	public addRight(t : BTree) : void{
		this.rt = t;
	}

	public sum() : number {return this.lt.sum() + this.rt.sum();}

	public height() : number {
		var left : number = this.lt.height();
		var right : number = this.rt.height();
		return (left > right) ? left : right;
	}
}


class Human {
	describe() : void { console.log("I'm a human");}
}

class Student {
	describe() : void { console.log("I'm a UCSD student");}
}

class Employee {
	describe() : void { console.log("I work at Google");}
}
