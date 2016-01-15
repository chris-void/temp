#include "share/atspre_staload.hats"

datatype 
avltree_t 
  (key:t@ype, value:t@ype, int) =
| AVL_leaf (key, value, 0) of ()
| {hl,hr:nat | ~1 <= hl-hr; hl-hr <= 1}
  AVL_node (key, value, 1+ max (hl, hr)) of 
    (key, value, avltree_t (key, value, hl), avltree_t(key, value, hr))

datasort 
AVLtree (int, int, int)= 
| {key,value:nat}
  leaf (key, value, 0) of ()
| {key,value:nat}{hl,hr:nat | ~1 <= hl-hr; hl-hr <= 1}
  node (key, value, 1+ max(hl, hr)) of (key, value, AVLtree (key, value, hl), AVLtree (key, value, hr))

typedef avltree_t (key:t@ype, value:t@ype) = [n:nat] avltree_t(key, value, n)
typedef cpm_t (a:t@ype) = (a, a) -<fun> Sgn

exception ElementAlreadyExists of ()
exception ElementDoesntExist   of ()

(* ***** ***** *)

fun 
{key:t@ype}{value:t@ype}
size
{h:nat}(
  tree: avltree_t (key, value, h)
): int h =
case+ tree of 
| AVL_leaf () => 0
| AVL_node (_, _, tl, tr) => size (tl) + size (tr)

fun
{key:t@ype}{value:t@ype}
height
{h:nat}(
  tree: avltree_t (key, value, h)
): int h =
case+ tree of
| AVL_leaf () => 0
| AVL_node (_, _, tl, tr) => max (height(tl), height(tr)) + 1

fun 
{key:t@ype}{value:t@ype}
shortestpath
{h:nat}(
  tree: avltree_t (key, value, h)
): int h = 
case+ tree of 
| AVL_leaf () => 0
| AVL_node (_, _, tl ,tr) => min (shortestpath(tl), shortestpath(tr))+ 1

fun 
{key:t@ype}{value:t@ype}
member
{h:nat}(
  tree: avltree_t(key, value, h), target: value, compare: cpm_t value
): bool = 
case+ tree of 
| AVL_leaf () => false 
| AVL_node (_ ,v, tl, tr) => begin 
    case+ compare (target, v) of 
   // | ~1 => member (tl, target, compare)
    |  1 => member (tr, target, compare)
    |  0 => true
    end 

fun 
{key:t@ype}{value:t@ype}
empty
( tree: avltree_t (key, value, h) ): bool = 
case+ tree of 
| AVL_leaf () => true
| _ => false 

(* ***** ***** *)
      
fun
{key:t@ype}{value:t@ype}
rotate_left
{hl,hr:nat | hr-hl==2}(
  k:key, v:value, tl: avltree_t(key, value, hl), tr:avltree_t(key, value, hr)
): [h:nat | hr <= h; h <= hr+1] avltree_t(key, value, h) = let
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

fun
{key:t@ype}{value:t@ype}
rotate_right
{hl,hr:nat | hl-hr==2}(
  k:key, v:value, tl:avltree_t(key, value, hl), tr:avltree_t(key, value, hr)
): [h:nat | hl <= h; h <= hl+1] avltree_t(key, value, h) = let
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


fun 
{key:t@ype} {value:t@ype} 
avltree_insert  (avltree (key, value), key, value, cmp: (key, key) -> int): avltree (key, value)

fun 
{key:t@ype} {value:t@ype} 
avltree_replace (avltree (key, value), key, value, cmp: (key, key) -> int): avltree (key, value)

fun 
{key:t@ype} {value:t@ype} 
avltree_delete  (avltree (key, value), key, cmp: (key, key) -> int): avltree (key, value)

fun 
{key:t@ype} {value:t@ype} 
avltree_lookup  (avltree (key, value), key, cmp: (key, key) -> int): maybe value

fun 
{key:t@ype} {value:t@ype} 
avltree_insert_or_replace (avltree (key, value), key, value, cmp: (key, key) -> int): avltree (key, value)

fun 
{key:t@ype} {value:t@ype} 
avltree_member  (avltree (key, value), key, cmp: (key, key) -> int): bool

fun avltree_empty  {key:t@ype} {value:t@ype} (avltree (key, value)): bool
fun avltree_size   {key:t@ype} {value:t@ype} (avltree (key, value)): size_t
fun avltree_height {key:t@ype} {value:t@ype} (avltree (key, value)): int

fun {key:t@ype} {value:t@ype} avltree_show (avltree (key, value), show_key: key -> void, show_value: value -> void): void 

