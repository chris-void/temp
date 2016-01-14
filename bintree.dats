#include "share/atspre_staload.hats"

(* ****** ****** *)

datasort btree = 
| leaf of ()
| node of (btree, btree)

(* ****** ****** *)

// size 
dataprop btree_size (btree, int)=
| btree_size_l (leaf (), 0) of ()
| {t1, t2:btree}{n1,n2:nat}
  btree_size_n (node (t1, t2), n1+n2+1) of (btree_size(t1, n1), btree_size(t2,n2))
  
dataprop btree_height (btree, int)=
| btree_height_l (leaf (), 0) of ()
| {t1,t2:btree}{n1,n2:nat}
  btree_height_n (node (t1, t2), max (n1,n2) +1) of (btree_height(t1, n2), btree_height(t2,n2))
  
dataprop btree_shortestpath (btree, int)=
| btree_shortestpath_l (leaf(), 0) of ()
| {t1,t2:btree}{n1,n2:nat}
  btree_shortestpath_n (node (t1, t2), min(n1, n2)+1) of (btree_shortestpath(t1, n1), btree_shortestpath(t2,n2))
  
(* ****** ****** *)
(*
prfun 
btree_height_isfun 
{t:btree}{n1,n2:nat} .<t>.
(
  pf1: btree_height(t, n1), pf2: btree_height(t,n2)
): [n1==n2] void = 
case+ (pf1, pf2) of 
| (btree_height_l (), btree_height_l ()) => ()
| (btree_height_n (pf11, pf12), btree_height_n (pf21, pf22)) => let 
    prval () = btree_height_isfun (pf11, pf21) 
    prval () = btree_height_isfun (pf12, pf22)
  in
  // empty
  end
*)
prfun btree_height_isfun {t:btree} {n1,n2:nat} .<t>.
  (pf1: btree_height (t, n1), pf2: btree_height (t, n2)): [n1==n2] void =
  case+ (pf1, pf2) of
  | (btree_height_n (pf11, pf12), btree_height_n (pf21, pf22)) => let
      prval () = btree_height_isfun (pf11, pf21) and () = btree_height_isfun (pf12, pf22)
    in
      // empty
    end // end of [btht_B, btht_B]
  | (btree_height_l (), btree_height_l ()) => ()
// end of [btht_isfun]

prfun btree_size_isfun
{t:btree}{n1,n2:nat} .<t>.
(
  pf1: btree_size(t, n1), pf2: btree_size(t,n2)
): [n1==n2] void = 
case+ (pf1, pf2) of 
| (btree_size_l (), btree_size_l ()) => ()
| (btree_size_n(pf11, pf12), btree_size_n(pf21, pf22)) => let 
    prval () = btree_size_isfun (pf11, pf21) 
    prval () = btree_size_isfun (pf12, pf22)
    in 
    // empyt
    end

prfun btree_shortestpath_isfun
{t:btree}{n1,n2:nat} .<t>.
(
  pf1: btree_shortestpath(t,n1), pf2: btree_shortestpath(t, n2)
): [n1==n2] void = 
case+ (pf1, pf2) of 
| (btree_shortestpath_l (), btree_shortestpath_l ()) => ()
| (btree_shortestpath_n (pf11, pf12), btree_shortestpath_n (pf21, pf22)) => let
    prval () = btree_shortestpath_isfun (pf11, pf21) 
    prval () = btree_shortestpath_isfun (pf12, pf22)
  in
    //empty
  end

(* ****** ****** *)
//prfun btree_height_istot
//prfun btree_size_istot
//prfun btree_shortestpath_istot
(* ****** ****** *)

dataprop isAvl (btree) = 
| isAvl_l (leaf ())
| {t1,t2:btree}{n1,n2:nat | n1 <= n2+1; n2 <= n1+1}
  isAvl_n (node(t1, t2)) of (isAvl t1, isAvl t2, btree_height(t1, n1), btree_height(t2, n2))

// prove AVL tree is balanced
prfun lemma_existence 
{t:btree}{shortestpath,height:nat} .<t>.
(
  pf_avl: isAvl (t), pf_shortestpath: btree_shortestpath (t, shortestpath), pf_height: btree_height (t, height) 
): [height <= shortestpath+shortestpath] void = 
case+ pf_avl of 
| isAvl_l () => let 
    prval btree_height_l () = pf_height
    prval btree_shortestpath_l () = pf_shortestpath
  in
    //empty
  end
| isAvl_n (pf1_avl, pf2_avl, pf1_height, pf2_height) => let
    prval btree_height_n (pf1_height_, pf2_height_) = pf_height
    prval btree_shortestpath_n (pf1_shortestpath, pf2_shortestpath) = pf_shortestpath
    prval () = btree_height_isfun (pf1_height, pf1_height_)
    prval () = btree_height_isfun (pf2_height, pf2_height_) 
    prval () = lemma_existence (pf1_avl, pf1_shortestpath, pf1_height)
    prval () = lemma_existence (pf2_avl, pf2_shortestpath, pf2_height)
  in
    //empty
  end