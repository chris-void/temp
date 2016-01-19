# Winter-break Project

**File included**
+ avl.dats   
Main file of this project, explain in details later   

+ tree.[d|s]ats   
Start these two files first in order to understand and improve the project in a better way    

+ README.md   
Descriptions and thoughts about this winter-break project    

+ /Atom-setting
While I coding the project, I found using *Atom* with *rmate* on a server, say Ubuntu Server, a very decent way. So I create the Atom setting files.(They are built from the [sublime setting](https://github.com/steinwaywhw/ats-mode-sublimetext).)

## Explanation
+ Theorem Proving part is finished all on my own work. Such as, dataprop, xxx_isfun, xxx_istot, etc.
+ Some of the functional part is referred from the avl.sats. I either wrote some part on my own or applied those on avltree.dats. I must acknowledge that follow others' programming paradigm is not as good as I wrote all of them from thin air.
+ All of the code passed type checking.

## Reference
As I understood that refer code is very important in ATS programming, here is mainly the code I referred from:

[tree.dats](https://github.com/githwxi/ATS-Postiats/blob/master/doc/BOOK/INT2PROGINATS/CODE/CHAP_THMPRVING/tree.dats)
---
This file basically gave me the fundamental structure of avltree.dats and I wrote the tree.[d|s]ats as a improvement of it.    
I also came up with the ideas of how to implement the theorem proving part of avltree.dats from it.


[avl.sats](https://github.com/steinwaywhw/ats-utils/blob/master/avl.sats)
---
Some functions of avltree.dats is altered from this file. They are rotate_left, rotate_right, replace, delete, insert_or_delete.
