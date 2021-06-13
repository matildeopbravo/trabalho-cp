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

// (4.5) Traces ----------------------------------------------------------------
let rec union a b =
    match b with
    | [] -> a
    | h::t when List.contains h a -> union a t
    | h::t -> h::(union a t)
    
let tunion (a, (l, r)) = union (List.map (fun x -> a::x) l) (List.map (fun x -> a::x) r)
let traces x = cataBTree (either (konst [[]]) tunion) x

// (4.6) Towers of Hanoi -------------------------------------------------------
let present = inord
let strategy (d, n) = if n = 0 then i1 () else i2 ((n - 1, d), ((not d, n - 1), (not d, n - 1)))

let hanoi x = hyloBTree present strategy x

// The Towers of Hanoi problem comes from a puzzle marketed in 1883
// by the French mathematician Édouard Lucas, under the pseudonym
// Claus. The puzzle is based on a legend according to which
// there is a temple, apparently in Bramah rather than in Hanoi as
// one might expect, where there are three giant poles fixed in the
// ground. On the first of these poles, at the time of the world's
// creation, God placed sixty four golden disks, each of different
// size, in decreasing order of size. The Bramin monks were given
// the task of moving the disks, one per day, from one pole to another
// subject to the rule that no disk may ever be above a smaller disk.
// The monks' task would be complete when they had succeeded in moving
// all the disks from the first of the poles to the second and, on
// the day that they completed their task the world would come to
// an end!

// There is a well­known inductive solution to the problem given
// by the pseudocode below. In this solution we make use of the fact
// that the given problem is symmetrical with respect to all three
// poles. Thus it is undesirable to name the individual poles. Instead
// we visualize the poles as being arranged in a circle; the problem
// is to move the tower of disks from one pole to the next pole in
// a specified direction around the circle. The code defines H n d
// to be a sequence of pairs (k,d') where n is the number of disks,
// k is a disk number and d and d' are directions. Disks are numbered
// from 0 onwards, disk 0 being the smallest. (Assigning number 0
// to the smallest rather than the largest disk has the advantage
// that the number of the disk that is moved on any day is independent
// of the total number of disks to be moved.) Directions are boolean
// values, true representing a clockwise movement and false an anti­clockwise
// movement. The pair (k,d') means move the disk numbered k from
// its current position in the direction d'. The semicolon operator
// concatenates sequences together, [] denotes an empty sequence
// and [x] is a sequence with exactly one element x. Taking the pairs
// in order from left to right, the complete sequence H n d prescribes
// how to move the n smallest disks one­by­one from one pole to the
// next pole in the direction d following the rule of never placing
// a larger disk on top of a smaller disk.

// H 0     d = [],
// H (n+1) d = H n ¬d ; [ (n, d) ] ; H n ¬d.

// (excerpt from R. Backhouse, M. Fokkinga / Information Processing
// Letters 77 (2001) 71--76)


// (5) Depth and balancing (using mutual recursion) --------------------------
let baldepth n =
    let h (a, ((b1, b2), (d1, d2))) = (b1 && b2 && abs (d1 - d2) <= 1, 1 + max d1 d2)
    let f ((b1, d1), (b2, d2)) = ((b1, b2), (d1, d2))
    let g x = either (konst (true, 1)) (h << (id >< f)) x
    cataBTree g n

let balBTree x = (p1 << baldepth) x
let depthBTree x = (p2 << baldepth) x
