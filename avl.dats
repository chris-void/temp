
#include "share/atspre_staload.hats"

exception ElemExisted  of ()
exception ElemNotExist of ()

(*
** AVL tree in proof form
*)
datasort
AVLtree =
| leaf of ()
| node of (AVLtree, AVLtree)
// end of [AVLtree]

dataprop
AVLequal (AVLtree, AVLtree) =
| AVLequal_l (leaf, leaf) of ()
| {tll,tlr:AVLtree}{trl,trr:AVLtree}
  AVLequal_n (node (tll, tlr), node (trl, trr)) of
    (AVLequal (tll, trl), AVLequal(tlr, trr))
// end of [AVLequal]

(* AVL tree height *)
dataprop
AVLheight (AVLtree, int) =
| AVLheight_l (leaf (), 0) of ()
| {tl,tr:AVLtree}{h1,h2:nat}
  AVLheight_n (node (tl, tr), 1+ max(h1, h2)) of
    (AVLheight(tl, h1), AVLheight(tr, h2))
// end of [AVLheight]

(* AVL tree size *)
dataprop
AVLsize (AVLtree, int) =
| AVLsize_l (leaf (), 0) of ()
| {tl,tr:AVLtree}{s1,s2:nat}
  AVLsize_n (node (tl, tr), s1+s2+1) of (AVLsize(tl, s1), AVLsize(tr, s2))
// end of [AVLsize]

(* AVL tree shortest path *)
dataprop
AVLshortestpath (AVLtree, int) =
| AVLshortestpath_l (leaf (), 0) of ()
| {tl,tr:AVLtree}{sp1,sp2:nat}
  AVLshortestpath_n (node (tl, tr), 1+ min (sp1, sp2)) of
    (AVLshortestpath(tl, sp1), AVLshortestpath(tr, sp2))
// end of [shortestpath]

dataprop isAVL (AVLtree) =
| isAVL_l (leaf ()) of ()
| {tl,tr:AVLtree} {n1,n2:nat | n1 <= n2+1; n2 <= n1+1}
  isAVL_n (node (tl, tr)) of
    (isAVL tl, isAVL tr, AVLheight (tl, n1), AVLheight (tr, n2))
// end of [isAVL]

(* ***** ***** *)

(*
  -> seems not necessary

// prove that AVLequal is functional
prfun
AVLequal_isfun{tl,tr:AVLtree}
(pf1: AVLtree, pf2: AVLtree) =
*)

(*  prove that AVLsize is a total relation on the two arguments  *)
prfun
AVLsize_istot {t:AVLtree} .<t>. (
  ): [s:nat] AVLsize (t, s) =
scase t of
| leaf () => AVLsize_l ()
| node (tl, tr) => AVLsize_n (AVLsize_istot{tl} (), AVLsize_istot{tl} ())
// end of [AVLsize_istot]

(*  prove that AVLsize is functional on the two arguments  *)
prfun
AVLsize_isfun{t:AVLtree}{s1,s2:nat} .<t>.
(
  pf1: AVLsize (t, s1), pf2: AVLsize(t, s2)
): [s1==s2] void =
case+ (pf1, pf2) of
| (AVLsize_l (), AVLsize_l ()) => ()
| (AVLsize_n (pf11, pf12), AVLsize_n (pf21, pf22)) =>
  let
    prval () = AVLsize_isfun (pf11, pf21)
    prval () = AVLsize_isfun (pf12, pf22)
  in
    //empty
  end
// end of [AVLsize_isfun]


(*  prove that AVLheight is a total relation on two arguments  *)
prfun
AVLheight_istot {t:AVLtree} .<t>. (
  ): [h:nat] AVLheight (t, h) =
scase t of
| leaf () => AVLheight_l ()
| node (tl, tr) => AVLheight_n (AVLheight_istot{tl} (), AVLheight_istot {tr} ())
// end of [AVLheight_istot]

(*  prove that AVLheight is functional on the two arguments  *)
prfun
AVLheight_isfun{t:AVLtree}{h1,h2:nat} .<t>.
(
  pf1: AVLheight (t, h1), pf2: AVLheight (t, h2)
): [h1==h2] void =
case+ (pf1, pf2) of
| (AVLheight_l (), AVLheight_l ()) => ()
| (AVLheight_n (pf11, pf12), AVLheight_n (pf21, pf22)) =>
  let
    prval () = AVLheight_isfun (pf11, pf21)
    prval () = AVLheight_isfun (pf12, pf22)
  in
    //empty
  end
// end of [AVLheight_isfun]


(*  prove that AVLshortestpath is a total relation on two arguments  *)
prfun
AVLshortestpath_istot {t:AVLtree} .<t>. (
  ): [sp:nat] AVLshortestpath (t, sp) =
scase t of
| leaf () => AVLshortestpath_l ()
| node (tl, tr) =>
    AVLshortestpath_n (AVLshortestpath_istot{tl}(), AVLshortestpath_istot{tr}())
// end of [AVLshortestpath_istot]

(*  prove that AVLshortestpath is functional on the two arguments  *)
prfun
AVLshortestpath_isfun{t:AVLtree}{sp1,sp2:nat} .<t>.
(
  pf1: AVLshortestpath (t,sp1), pf2: AVLshortestpath (t, sp2)
): [sp1==sp2] void =
case+ (pf1, pf2) of
| (AVLshortestpath_l (), AVLshortestpath_l ()) => ()
| (AVLshortestpath_n (pf11, pf12), AVLshortestpath_n (pf21, pf22)) =>
  let
    prval () = AVLshortestpath_isfun (pf11, pf21)
    prval () = AVLshortestpath_isfun (pf12, pf22)
  in
    //empty
  end
// end of [AVLshortestpath_isfun]

(* ***** ***** *)

(*
** AVL tree using independent type
*)
datatype
avltree (key:t@ype, value:t@ype, int(*height*)) =
| AVL_leaf (key, value, 0) of ()
| {hl,hr:nat | ~1 <= hl-hr; hl-hr <= 1}
  AVL_node (key, value, 1+ max (hl, hr)) of
    (key, value, avltree (key, value, hl), avltree(key, value, hr))
// end of [avltree]

typedef avltree (key:t@ype, value:t@ype) = [n:nat] avltree(key, value, n)

typedef avltree_inc (key:t@ype, value: t@ype, h:int) =
  [h1:nat | h <= h1; h1 <= h+1] avltree (key, value, h1)
// end of [avltree_inc]

typedef avltree_dec (key:t@ype, value:t@ype, h:int) =
  [h1:nat | h1 <= h; h <= h1+1] avltree (key, value, h1)
// end of [avltree_dec]

(*  AVL tree height  *)
fun
{key:t@ype}{value:t@ype}
height
{h:nat}(
  tree: avltree (key, value, h)
): int h =
case+ tree of
| AVL_leaf () => 0
| AVL_node (_, _, tl, tr) => 1+ max (height (tl), height (tr))
// end of [height]

(*  AVL tree shortest path  *)
fun
{key:t@ype}{value:t@ype}
shortestpath
{h:nat}(
  tree: avltree (key, value, h)
): int =
case+ tree of
| AVL_leaf () => 0
| AVL_node (_, _, tl ,tr) => 1+ min (shortestpath(tl), shortestpath(tr))
// end of [height]

(*  AVL tree size  *)
fun
{key:t@ype}{value:t@ype}
size
{h:nat}(
  tree: avltree (key, value, h)
): int =
case+ tree of
| AVL_leaf () => 0
| AVL_node (_, _, tl, tr) => 1+ size(tl) + size(tr)
// end of [size]

(*  if the element is a member of this tree  *)
fun
{key:t@ype}{value:t@ype}
isMember
{h:nat}(
  tree: avltree (key, value, h), k: key, cmp: (key, key) -> int
): bool =
case+ tree of
| AVL_leaf () => false
| AVL_node  (current, _, tl, tr) =>
    if cmp (current, k) = 0 then true
    else if cmp (current, k) > 0
      then isMember (tl, k, cmp)
      else isMember (tr, k, cmp)
// end of [isMember]

fun
{key:t@ype}{value:t@ype}
isEmpty
{h:nat}(
  tree: avltree (key, value, h)
): bool =
case+ tree of
| AVL_leaf () => true
| _ => false
// end of [isEmpty]

fun
{key:t@ype}{value:t@ype}
isPerfect
{h:nat}(
  tree: avltree(key, value, h)
): bool =
case+ tree of
| AVL_leaf () => true
| AVL_node (_, _, tl, tr) =>
    isPerfect(tl) && isPerfect(tr) && height(tl) = height(tr)
// end of [isPerfect]

(* ***** ***** *)

fun
{key:t@ype}{value:t@ype}
rotate_left
{hl,hr:nat | hr-hl==2}(
  k:key, v:value, tl: avltree(key, value, hl), tr:avltree(key, value, hr)
): [h:nat | hr <= h; h <= hr+1] avltree(key, value, h) = let
  val AVL_node (rkey, rvalue, rl, rr) = tr
in
  if height(rl) <= height(rr)
  then AVL_node (rkey, rvalue, AVL_node(k, v, tl, rl), rr)
  else let
    val AVL_node (rlk, rlv, rll, rlr) = rl
  in
    AVL_node (rlk, rlv, AVL_node(k,v, tl, rll), AVL_node (rkey, rvalue, rlr, rr))
  end
end
// end of [rotate_left]

fun
{key:t@ype}{value:t@ype}
rotate_right
{hl,hr:nat | hl-hr==2}(
  k:key, v:value, tl:avltree(key, value, hl), tr:avltree(key, value, hr)
): [h:nat | hl <= h; h <= hl+1] avltree(key, value, h) = let
  val AVL_node (lk, lv, ll, lr)= tl
in
  if height (ll) >= height (lr)
  then AVL_node (lk, lv, ll, AVL_node (k, v, lr, tr))
  else let
    val AVL_node (lrk, lrv, lrl, lrr) = lr
  in
    AVL_node (lrk, lrv, AVL_node (lk, lv, ll, lrl), AVL_node (k, v, lrr, tr))
  end
end
// end of [rotate_right]

(* ***** ***** *)

fun
{key:t@ype}{value:t@ype}
avltree_insert
{h:nat}(
  tree: avltree (key, value, h), k: key, v: value, cmp: (key, key) -> int
): [hh:nat|h <= hh; hh <= h+1] avltree (key, value, hh) =
case+ tree of
| AVL_leaf () => AVL_node (k, v, AVL_leaf (), AVL_leaf ())
| AVL_node (current_key, current_value, left, right) =>
  if cmp (k, current_key) < 0
  then let
    val t = avltree_insert (left, k, v,cmp)
  in
    if height t - height right > 1
    then rotate_right (current_key, current_value, t, right)
    else AVL_node (current_key, current_value, t, right)
  end
  else if cmp (k, current_key) > 0
    then let
      val t = avltree_insert (right, k, v, cmp)
    in
      if height t - height left > 1
      then rotate_left (current_key, current_value, left, t)
      else AVL_node (current_key, current_value, left, t)
    end
  else
    $raise ElemExisted ()

fun
{key:t@ype} {value:t@ype}
avltree_replace
(
  tree: avltree (key, value), k: key, v: value, cmp: (key, key) -> int
): avltree (key, value) =
case+ tree of
| AVL_leaf () => $raise ElemNotExist ()
| AVL_node (current, _, left, right) =>
  if cmp (k, current) > 0
  then avltree_replace (right, k, v, cmp)
  else if cmp (k, current) < 0
    then avltree_replace (left, k, v, cmp)
    else AVL_node (current, v, left, right)


fun
{key:t@ype} {value:t@ype}
avltree_findmin
{h:nat}(
  tree: avltree (key, value, h)
): (key, value) =
case+ tree of
| AVL_node (k, v, AVL_leaf (), _) => (k, v)
| AVL_node (_, _, left, _) => avltree_findmin (left)
| AVL_leaf () => $raise ElemNotExist ()


fun
{key:t@ype} {value:t@ype}
avltree_delete
{h:nat}(
  tree: avltree (key, value, h), k:key, cmp: (key, key) -> int
): [hh:nat|h-1 <= hh; hh <= h] avltree (key, value, hh) =
case+ tree of
| AVL_leaf () => $raise ElemNotExist ()
| AVL_node (current, _, AVL_leaf (), AVL_leaf ()) =>
  if cmp (current, k) = 0
  then AVL_leaf ()
  else $raise ElemNotExist ()
| AVL_node (current, v, tl, tr) =>
  if cmp (k, current) < 0
  then let
    val newleft = avltree_delete (tl, k, cmp)
  in
    if height (tr) - height newleft > 1
    then rotate_left (current, v, newleft, tr)
    else AVL_node (current, v, newleft, tr)
  end
  else if cmp (k, current) > 0
    then let
      val newright = avltree_delete (tr, k, cmp)
    in
      if height (tl) - height newright > 1
      then rotate_right (current, v, tl, newright)
      else AVL_node (current, v, tl, newright)
    end else
    case+ (tl, tr) of
    | (AVL_leaf (), _) => tr
    | (_, AVL_leaf ()) => tl
    | (_, _) => let
        val (mink, minv) = avltree_findmin (tr)
        val newright = avltree_delete (tr, mink, cmp)
      in
        if height (tl) - height newright > 1
        then rotate_right (mink, minv, tl, newright)
        else AVL_node (mink, minv, tl, newright)
      end

fun
{key:t@ype} {value:t@ype}
avltree_insert_or_replace
(
  tree: avltree (key, value), k:key, v:value, cmp: (key, key) -> int
): avltree (key, value) =
if isMember (tree, k, cmp)
then avltree_replace (tree, k, v, cmp)
else avltree_insert (tree, k, v, cmp)
(*
fun
{key:t@ype} {value:t@ype}
avltree_concat
{h1,h2:nat}(
  t1: avltree(key, value, h1), t2: avltree(key, value, h2)
) [h:nat] avltree(key, value, h) =
case+ (t1, t2) of
| (AVL_leaf (), _) => t1
| (_, AVL_leaf ()) => t2
| (_, _) =>>


fun
{key:t@ype} {value:t@ype}
avltree_takeout_min
{h:nat} .<h>. (
  t: avltree(key, value, h), cmpk: (key, key) -> int, cmpv: (value, value) -> int
): avltree_dec (key, value, h) = let
  val+ AVL_node (k, v, tl, tr) = t
in
  case+ tl of
  | AVL_leaf () => (key, value, )
  | AVL_node

*)
fun
{key:t@ype} {value:t@ype}
avltree_leftjoin
{hl,hr:nat | hl >= hr} .<hl>. (
  k: key, v: value
, tl: avltree (key, value, hl)
, tr: avltree (key, value, hr)
):  avltree (key, value, hl) = let
  val hl = height (tl) and hr = height (tr)
in
  if hl >= hr + 2
  then let
    val+ AVL_node{hll,hlr} (kl, vl, tll, tlr) = tl
    val [hlr:int] tlr = avltree_leftjoin (k, v, tlr, tr)
    val hll = height (tll)
    val hlr = height (tlr)
  in
    if hlr <= hll + 1
    then AVL_node{hll,hlr} ( kl, vl, tll, tlr)
    else rotate_left (kl, vl, tll, tlr)
  end else AVL_node{hl,hr} (k, v, tl, tr)
end

(*
fun
{key:t@ype} {value:t@ype}
avltree_takeout_min
  {h:nat} .<h>. (
  t: avltree (key, value, h), x0: &a? >> a
) :<> avltree_dec (key, value, h) = let
  val+ B {..} {hl,hr} (k, v, tl, tr) = t
in
  case+ tl of
  | B _ => let
      val [hl:int] tl = avltree_takeout_min<a> (tl, x0)
      val hl = avltree_height (tl) : int hl
      and hr = avltree_height (tr) : int hr
    in
      if hr - hl <= HTDF then begin
        B (1+max(hl,hr), x, tl, tr)
      end else begin // hl+HTDF1 = hr
        avltree_lrotate (x, hl, tl, hr, tr)
      end // end of [if]
    end // end of [B]
  | E () => (x0 := x; tr)
end // end of [avltree_takeout_min]

(* ****** ****** *)

implement{a}
funset_remove
  (m, x0, cmp) = b(*removed*) where {
  fun remove {h:nat} .<h>. (
    t: avltree (a, h), b: &bool? >> bool
  ) :<cloref> avltree_dec (a, h) = begin
    case+ t of
    | B {..} {hl,hr} (h, x, tl, tr) => let
        val sgn = compare_elt_elt (x0, x, cmp)
      in
        case+ 0 of
        | _ when sgn < 0 => let
            val [hl:int] tl = remove (tl, b)
            val hl = avltree_height (tl) : int hl
            and hr = avltree_height (tr) : int hr
          in
            if hr - hl <= HTDF then
              B (1+max(hl,hr), x, tl, tr)
            else // hl+HTDF1 = hr
              avltree_lrotate (x, hl, tl, hr, tr)
            // end of [if]
          end // end of [sgn < 0]
        | _ when sgn > 0 => let
            val [hr:int] tr = remove (tr, b)
            val hl = avltree_height (tl) : int hl
            and hr = avltree_height (tr) : int hr
          in
            if hl - hr <= HTDF then
              B (1+max(hl,hr), x, tl, tr)
            else // hl=hr+HTDF1
              avltree_rrotate (x, hl, tl, hr, tr)
            // end of [if]
          end // end of [sgn > 0]
        | _ (*sgn = 0*) => let
            val () = b := true
          in
            case+ tr of
            | B _ => let
                var x_min: a?
                val [hr:int] tr = avltree_takeout_min<a> (tr, x_min)
                val hl = avltree_height (tl) : int hl
                and hr = avltree_height (tr) : int hr
              in
                if hl - hr <= HTDF then
                  B (1+max(hl,hr), x_min, tl, tr)
                else // hl=hr+HTDF1
                  avltree_rrotate (x_min, hl, tl, hr, tr)
                // end of [if]
              end // end of [B]
            | E _ => tl
          end // end of [sgn = 0]
      end // end of [B]
    | E () => t where {
        val () = b := false
      } // end of [E]
  end // end of [remove]
  var b: bool // unitialized
  val () = m := remove (m, b)
} // end of [funset_remove]

(* ****** ****** *)

(*
** left join: height(tl) >= height(tr)
*)
fun{a:t@ype}
avltree_ljoin
  {hl,hr:nat | hl >= hr} .<hl>. (
  x: a, tl: avltree (a, hl), tr: avltree (a, hr)
) :<> avltree_inc (a, hl) = let
  val hl = avltree_height (tl): int hl
  and hr = avltree_height (tr): int hr
in
  if hl >= hr + HTDF1 then let
    val+ B {..} {hll, hlr} (_, xl, tll, tlr) = tl
    val [hlr:int] tlr = avltree_ljoin<a> (x, tlr, tr)
    val hll = avltree_height (tll): int hll
    and hlr = avltree_height (tlr): int hlr
  in
    if hlr <= hll + HTDF then
      B (max(hll,hlr)+1, xl, tll, tlr)
    else // hll+HTDF1 = hlr
      avltree_lrotate<a> (xl, hll, tll, hlr, tlr)
    // end of [if]
  end else begin
    B (hl+1, x, tl, tr)
  end // end of [if]
end // end of [avltree_ljoin]

(*
** right join: height(tl) <= height(tr)
*)
fun{a:t@ype}
avltree_rjoin
  {hl,hr:nat| hl <= hr} .<hr>. (
  x: a, tl: avltree (a, hl), tr: avltree (a, hr)
) :<> avltree_inc (a, hr) = let
  val hl = avltree_height (tl): int hl
  and hr = avltree_height (tr): int hr
in
  if hr >= hl + HTDF1 then let
    val+ B {..} {hrl,hrr} (_, xr, trl, trr) = tr
    val [hrl:int] trl = avltree_rjoin<a> (x, tl, trl)
    val hrl = avltree_height (trl): int hrl
    and hrr = avltree_height (trr): int hrr
  in
    if hrl <= hrr + HTDF then
      B (max(hrl,hrr)+1, xr, trl, trr)
    else // hrl = hrr+HTDF1
      avltree_rrotate (xr, hrl, trl, hrr, trr)
    // end of [if]
  end else begin
    B (hr+1, x, tl, tr)
  end // end of [if]
end // end of [avltree_rjoin]

(* ****** ****** *)

fn{a:t@ype}
avltree_join {hl,hr:nat} (
  x: a, tl: avltree (a, hl), tr: avltree (a, hr)
) :<> [h:int | hl <= h; hr <= h; h <= max(hl,hr)+1] avltree (a, h) = let
  val hl = avltree_height tl: int hl
  and hr = avltree_height tr: int hr
in
  if hl >= hr then avltree_ljoin (x, tl, tr) else avltree_rjoin (x, tl, tr)
end // end of [avltree_join]

(* ****** ****** *)

fn{a:t@ype}
avltree_concat {hl,hr:nat} (
  tl: avltree (a, hl), tr: avltree (a, hr)
) :<> [h:nat | h <= max(hl,hr)+1] avltree (a, h) =
  case+ (tl, tr) of
  | (E (), _) => tr
  | (_, E ()) => tl
  | (_, _) =>> let
      var x_min: a // uninitialized
      val tr = avltree_takeout_min<a> (tr, x_min)
    in
      avltree_join (x_min, tl, tr)
    end // end of [_, _]
// end of [avltree_concat]
*)