define pred bst^(x): 
  ( ((x l= nil) & emp) |
	  ((x |-> loc left: lft; loc right: rgt; int key: ky) * ((bst^(lft) & (keys^(lft) set-lt ky)) * (bst^(rgt) & (ky lt-set keys^(rgt)))))  
  );


define set-fun keys^(x):
  (case (x l= nil): emptyset;
   case ((x |-> loc left: lft; loc right: rgt; int key: ky) * true): 
   	((singleton ky) union (keys^(lft) union keys^(rgt)));
   default: emptyset
  ) ;


method bst-search(loc x, int kk)
requires: (bst^(x) & (keys^(x) s= xks)) ;
ensures: (((ret i= 1) & (kk i-in xks)) | ((ret i= 0) & (~ (kk i-in xks)))) ;


bb bst-search-nil:
pre: (bst^(x) & (keys^(x) s= xkss)) ;
post: (((ret i= 1) & (k i-in xkss)) | ((ret i= 0) & (~ (k i-in xkss)))) ;
{
	assume (x l== nil);
	int ret := 0;
}

bb bst-search-basic:
pre: (bst^(x) & (keys^(x) s= xkss)) ;
post: (((ret i= 1) & (k i-in xkss)) | ((ret i= 0) & (~ (k i-in xkss)))) ;
{
	assume (! (x l== nil));
	int xk := x.key;
	assume (k i== xk);
	int ret := 1;
}

bb bst-search-left:
pre: (bst^(x) & (keys^(x) s= xkss)) ;
post: (((ret i= 1) & (k i-in xkss)) | ((ret i= 0) & (~ (k i-in xkss)))) ;
{
	assume (! (x l== nil));
	int xk := x.key;
	loc l := x.left;
	assume (! (k i== xk));
	assume (k < xk);
	int ret := bst-search(l; k);
}

bb bst-search-left-pre:
pre: (bst^(x) & (keys^(x) s= xkss)) ;
post: (bst^(l) * true) ;
{
	assume (! (x l== nil));
	int xk := x.key;
	loc l := x.left;
	assume (! (k i== xk));
	assume (k < xk);
}

bb bst-search-right:
pre: (bst^(x) & (keys^(x) s= xkss)) ;
post: (((ret i= 1) & (k i-in xkss)) | ((ret i= 0) & (~ (k i-in xkss)))) ;
{
	assume (! (x l== nil));
	int xk := x.key;
	loc r := x.right;
	assume (! (k i== xk));
	assume (! (k < xk));
	int ret := bst-search(r; k);
}

bb bst-search-right-pre:
pre: (bst^(x) & (keys^(x) s= xkss)) ;
post: (bst^(r) * true) ;
{
	assume (! (x l== nil));
	int xk := x.key;
	loc r := x.right;
	assume (! (k i== xk));
	assume (! (k < xk));
}















