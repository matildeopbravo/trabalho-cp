module BTree

open Cp

// (1) Datatype definition -----------------------------------------------------
type BTree<'a> = Empty | Node of 'a * (BTree<'a> * BTree<'a>)

let inBTree x = either (konst Empty) Node x
let outBTree x =
    match x with
    | Empty -> i1 ()
    | Node (a,(t1,t2)) -> i2 (a, (t1, t2))

// (2) Ana + cata + hylo -------------------------------------------------------
let baseBTree f g = id -|- (f >< (g >< g))
let recBTree g = baseBTree id g
let rec cataBTree g x = (g << recBTree (cataBTree g) << outBTree) x
let rec anaBTree g x = (inBTree << recBTree (anaBTree g) << g) x
let hyloBTree h g x = (cataBTree h << anaBTree g) x


// (3) Map ---------------------------------------------------------------------
let fmap f x = cataBTree (inBTree << baseBTree f id) x

// (4) Examples ----------------------------------------------------------------

// (4.1) Inmersion (mirror) ----------------------------------------------------
let invBTree x = cataBTree (inBTree << (id -|- (id >< swap))) x

// (4.2) Counting --------------------------------------------------------------
let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.3) Serialization ---------------------------------------------------------
let inord y =
    let join (x, (l, r)) = l @ [x] @ r
    either nil join y
let inordt x = cataBTree inord x // in-order traversal

let preord y =
    let f (x, (l, r)) = x::(l @ r)
    either nil f y
let preordt x = cataBTree preord x // pre-order traversal

let postordt y = // post-order traversal
    let f (x, (l, r)) = l @ r @ [x]
    cataBTree (either nil f) y

// (4.4) Quicksort -------------------------------------------------------------
let rec part p x =
    match x with
    | [] -> ([], [])
    | (h::t) -> let s, l = part p t
                if p h then (h::s,l) else (s,h::l)

let qsep x =
    match x with
    | [] -> i1 ()
    | (h::t) -> let s, l = part (fun n -> n < h) t
                i2 (h, (s, l))

let qSort x = hyloBTree inord qsep x
