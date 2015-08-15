(* SML bst - "pure" version *)

datatype tree = mt | node of tree * int * tree;

fun ints_from_to(min, max) =
	if min <= max then
		min :: ints_from_to (min+1, max)
	else 
		[];

fun bst_size(t) =
    case t of
	  mt => 0
    	| node (l, n, r) => 1 + bst_size(l) + bst_size(r);

fun bst_insert(x, t0) =
    case t0 of
    	  mt => node(mt, x, mt)
    	| node(l, n, r) =>
        	if x<=n then
            		node(bst_insert(x, l), n, r)
        	else
		    	node(l, n, bst_insert(x, r));

fun list_bst_acc(xs, t0) =
    case xs of
    	  [] => t0
    	| (x:: xs1) => list_bst_acc(xs1, bst_insert(x, t0));

fun list_bst(xs) = list_bst_acc(xs, mt);

fun test n = bst_size(list_bst(ints_from_to(1,n)));

print (Int.fmt StringCvt.DEC (test 30000));
print "\n";
