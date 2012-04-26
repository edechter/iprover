(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2010 Konstantin Korovin and The University of Manchester. 
   This file is part of iProver - a theorem prover for first-order logic.

   iProver is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   iProver is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
   See the GNU General Public License for more details.
   You should have received a copy of the GNU General Public License
   along with iProver.  If not, see <http://www.gnu.org/licenses/>.         *)
(*----------------------------------------------------------------------[C]-*)


module type Elem0 =
sig 

  (* The type of an element *)
  type t 

end

module type Ordered = 
sig

  (* The type of an element *)
  type t
    
  (* An ordering on elements *)
  val compare : t -> t -> int

end


exception EmptyHeap


module type HeapSig = sig

  type elt

  (* Type of imperative heaps.
     (In the following [n] refers to the number of elements in the heap) *)

  type t 

  (* [create c] creates a new heap, with initial capacity of [c] *)
  val create : (module Ordered) -> int -> t

  (* [is_empty h] checks the emptiness of [h] *)
  val is_empty : t -> bool

  (* [add x h] adds a new element [x] in heap [h]; size of [h] is doubled
     when maximum capacity is reached; complexity $O(log(n))$ *)
  val add : t -> elt -> unit

  (* [maximum h] returns the maximum element of [h]; raises [EmptyHeap]
     when [h] is empty; complexity $O(1)$ *)
  val maximum : t -> elt

  (* [remove h] removes the maximum element of [h]; raises [EmptyHeap]
     when [h] is empty; complexity $O(log(n))$ *)
  val remove : t -> unit

  (* [pop_maximum h] removes the maximum element of [h] and returns it;
     raises [EmptyHeap] when [h] is empty; complexity $O(log(n))$ *)
  val pop_maximum : t -> elt

  (* usual iterators and combinators; elements are presented in
     arbitrary order *)
  val iter : (elt -> unit) -> t -> unit
(* Old
  val fold : (X.t -> 'a -> 'a) -> t -> 'a -> 'a
*)
  val fold : ('a ->  elt -> 'a) -> t -> 'a -> 'a
end


module Heap(E : Elem0) = struct

  (* The type of an element in the heap *)
  type elt = E.t

  (* The heap is encoded in the array [data], where elements are stored
     from [0] to [size - 1]. From an element stored at [i], the left 
     (resp. right) subtree, if any, is rooted at [2*i+1] (resp. [2*i+2]). *)

  type t = { ordered_m : (module Ordered with type t = elt);
	     mutable size : int; 
	     mutable data : elt array }

 (* When [create n] is called, we cannot allocate the array, since there is
     no known value of type [X.t]; we'll wait for the first addition to 
     do it, and we remember this situation with a negative size. *)

  let create o n = 
    if n <= 0 then invalid_arg "create";
    { ordered_m = o;
      size = -n; 
      data = [||] }

  let is_empty h = h.size <= 0

  (* [resize] doubles the size of [data] *)

  let resize h =
    let n = h.size in
    assert (n > 0);
    let n' = 2 * n in
    let d = h.data in
    let d' = Array.create n' d.(0) in
    Array.blit d 0 d' 0 n;
    h.data <- d'

  let add h x =
    let module X = (val h.ordered_m : Ordered with type t = elt) in 
    (* first addition: we allocate the array *)
    if h.size < 0 then begin
      h.data <- Array.create (- h.size) x; h.size <- 0
    end;
    let n = h.size in
    (* resizing if needed *)
    if n == Array.length h.data then resize h;
    let d = h.data in
    (* moving [x] up in the heap *)
    let rec moveup i =
      let fi = (i - 1) / 2 in
      if i > 0 && X.compare d.(fi) x < 0 then begin
	d.(i) <- d.(fi);
	moveup fi
      end else
	d.(i) <- x
    in
    moveup n;
    h.size <- n + 1

  let maximum h =
    if h.size <= 0 then raise EmptyHeap;
    h.data.(0)

  let remove h =
    let module X = (val h.ordered_m : Ordered with type t = elt) in 
    if h.size <= 0 then raise EmptyHeap;
    let n = h.size - 1 in
    h.size <- n;
    let d = h.data in
    let x = d.(n) in
    (* moving [x] down in the heap *)
    let rec movedown i =
      let j = 2 * i + 1 in
      if j < n then
	let j = 
	  let j' = j + 1 in 
	  if j' < n && X.compare d.(j') d.(j) > 0 then j' else j 
	in
	if X.compare d.(j) x > 0 then begin 
	  d.(i) <- d.(j); 
	  movedown j 
	end else
	  d.(i) <- x
      else
	d.(i) <- x
    in
    movedown 0

  let pop_maximum h = let m = maximum h in remove h; m

  let iter f h = 
    let d = h.data in
    for i = 0 to h.size - 1 do f d.(i) done

  let fold f h x0 =
    let n = h.size in
    let d = h.data in
    let rec foldrec x i =
      if i >= n then x else foldrec (f x d.(i)) (succ i)
    in
    foldrec x0 0

end



(* An element in the priority queue *)
module type ElemN = 
sig

  (* The type of an element in the queue *)
  type t

  (* A comparison function between two elements for each queue *)
  val compare : t -> t -> int

  val equal : t -> t -> bool

  (* A flag for membership of an element in each queue *)
  val in_queue : t -> bool

  (* A function setting the membership flag for each queue *)
  val assign_in_queue : bool -> t -> unit

  (* The multiplier for each queue *)
  val mult : int
    
end


module QueueN (Elem0:Elem0) =
struct 


  (* The type of element in all queues *)
  type elt = Elem0.t


  (* The data structure for one queue *)
  type queue = { 

    (* The module of elements in the queue *)
    mutable m_elem : (module ElemN with type t = elt);

    (* The queue of elements *) 
    mutable queue : Heap(Elem0).t;

    (* The counter for the number of elements taken from the queue *)
    mutable mult : int 
      
  }


  (* The data structure for n queues *)
  type t = { 
  
    (* The list of queues *) 
    mutable queues : queue list; 
    
    (* Try to count the number of unique elements in the queues *)
    mutable num_elem : int 

  }
      

  (* All queues are empty *)
  exception Empty 


  (* Create n queues *)
  let create init_size (elems : (module ElemN with type t = elt) list) = 

    (* Local module binding at outermost level *)
    let module H = Heap(Elem0) in
    
    { queues = 
	
	(* Create one queue of each element module *)
	List.map 
	  (function e -> 

	    (* Get module from value *)
	    let module E = (val e : ElemN with type t = elt) in 

	    { 

	      (* Save module of elements *)
	      m_elem = e;
	      
	      (* Create heap from element *)
	      queue = 
		H.create 
		  (module E : Ordered with type t = elt) 
		  init_size;

	      (* Initialise modulus counter *)
	      mult = 0 

	    })
	  elems;

      (* Initialise counter of elements *)
      num_elem = 0 }


  (* Add an element to all queues *)
  let add_all ({ queues = queue_n } as q) elem = 

    (* Local module binding at outermost level *)
    let module H = Heap(Elem0) in

    (* Add element to all queues *)
    List.iter 
      (function { m_elem; queue; _ } -> 

	(* Get module from value *)
	let module E = (val m_elem : ElemN with type t = elt) in 
	
	(* Element not already in queue? *)
	if not (E.in_queue elem) then

	  (

	    (* Add element to queue *)
	    H.add queue elem;

	    (* Flag element as in queue *)
	    E.assign_in_queue true elem

	  ))
      queue_n;
    
    (* Increment counter of elements in queue *)
    q.num_elem <- succ q.num_elem
    
	
  (* All queues are empty? *)
  let is_empty { queues = queue_n } = 

    (* Local module binding at outermost level *)
    let module H = Heap(Elem0) in
    
    (* All queues are empty? *)
    List.for_all
      (function { queue } -> H.is_empty queue)
      queue_n


  (* Clean queues *)
  let clean init_size { queues = queue_n } =
  
    (* Local module binding at outermost level *)
    let module H = Heap(Elem0) in

    List.iter
      (function { m_elem; queue } as q -> 

	(* Get module from value *)
	let module E = (val m_elem : ElemN with type t = elt) in 

	(* Flag all elements in queue as not in queue *)
	H.iter (E.assign_in_queue false) queue;

	(* Recreate queue *)
	q.queue <- 
	  H.create (module E : Ordered with type t = elt) init_size)
      queue_n


  (* Remove first element from the next priority queue *)
  let rec remove' ({ queues = queue_n; num_elem } as all_q) = 
    
    (* Local module binding at outermost level *)
    let module H = Heap(Elem0) in function 

      (* No element to remove from any queue?

	 Not every queue is empty, this has to be checked by the
	 calling function, otherwise we will loop infinitely. *)
      | [] -> 

	(* Reset modulus counters in all queues to their maximum *)
	List.iter
	  (function ({ m_elem } as q) -> 
	    let module E = (val m_elem : ElemN with type t = elt) in 
	    q.mult <- E.mult)
	  queue_n;

	(* Restart search for element to remove *)
	remove' all_q queue_n

      (* First queue is not empty and the modulus counter is not 0? *)
      | ({ queue; m_elem; mult } as q) :: tl 
	  when mult > 0 && not (H.is_empty queue) -> 
	
	(
	  
	  (* Module for elements in this queue *)
	  let module E = (val m_elem : ElemN with type t = elt) in 

	  (* Take first element from the queue *)
	  let elem = H.maximum queue in
	  
	  (* Check if element has not been removed from queue *)
	  if E.in_queue elem then
	  
	    (

	      (* Flag element as removed from every queue *)
	      List.iter 
		(function { m_elem } -> 
		  let module E = (val m_elem : ElemN with type t = elt) in 
		  E.assign_in_queue false elem)
		queue_n;
	      
	      (* Decrement modulus counter of queue *)
	      q.mult <- pred mult;
	      
	      all_q.num_elem <- pred num_elem;

	      (* Return element *)
	      elem
		
	    )
	      
	  (* Element has been removed from this queues *)
	  else
	    
	    (* Remove next element from this queue *)
	    remove' all_q (q :: tl)
	)
	  
      (* First queue is empty or modulus counter is 0 *)
      | _ :: tl -> 
	
	(* Try to remove from some next queue *)
	remove' all_q tl 
	

  (* Remove first element from the next priority queue *)
  let remove ({ queues = queue_n } as q) = 

    (* All queues are empty? *)
    if is_empty q then 

      (* Raise exception *)
      raise Empty 

    else 
      
      (* Remove some element from some queue *)
      remove' q queue_n
	
end
  









(* after element is added it is always in both queues *)
(* if is was in one of the queues the it is not added again to this queue *)
(* if element is removed it is first checked is it is in the other queue *)
(* if not then it is discarded not affecting the ratio *)
(* queue is empty if at least one of the queues is empty*)



module Queue (Elem:Elem) = 
struct

  module QueueElem = 
  struct
    type t = Elem.t
    let compare = Elem.compare
    end
  module Queue1 = Heap.Imperative (Queue1Elem) 

  module Queue2Elem = 
    struct
      type t      = Elem2.t
      let compare = Elem2.compare2
    end
  module Queue2 = Heap.Imperative (Queue2Elem) 


  type t = { mutable queues : Queue1.t list; 
	     mutable current_mult : int list;
	     mutable num_elem : int }

  let create init_size = 

    let rec create_queue accum = function

      | [] -> accum

      | 



    { queue1 = Queue1.create (init_size);
      queue2 = Queue2.create (init_size);
      current_mult1 = Elem2.mult1;
      current_mult2 = Elem2.mult2;
      num_elem      = 0;
   }

  let num_elem queue = queue.num_elem

  let add queue t = 
    let in_q1 = (Elem2.in_queue1 t) in
    let in_q2 = (Elem2.in_queue2 t) in
   if ((not in_q1) || (not in_q2))
   then 
     (queue.num_elem <- queue.num_elem+1;
      (if (not in_q1)
      then 
	(Queue1.add queue.queue1 t;
	 Elem2.assign_in_queue1  true t
	)
      else ());
      (if (not in_q2)
      then 
	(Queue2.add queue.queue2 t;
	 Elem2.assign_in_queue2 true t
	)
      else ())
     )
   else ()

  exception Empty 
	
  let is_empty queue = 
    if ((Queue1.is_empty queue.queue1) || (Queue1.is_empty queue.queue1))
    then true else false 

  let clean init_size queue = 
    Queue1.iter (Elem2.assign_in_queue1 false) queue.queue1;
    Queue2.iter (Elem2.assign_in_queue2 false) queue.queue2;
    queue.queue1 <- Queue1.create (init_size);
    queue.queue2 <- Queue2.create (init_size);
    queue.num_elem <- 0
     

  let rec remove queue = 
    if (is_empty queue) then raise Empty 
    else
      (
       if ((queue.current_mult1 > 0) & 
	   (not (Queue1.is_empty queue.queue1)))
       then 
	 (let t =  Queue1.maximum queue.queue1 in 
	 Queue1.remove queue.queue1;     
	 Elem2.assign_in_queue1 false t;
	 if (not (Elem2.in_queue2 t)) 
	 then remove queue	      
	 else 
	   (queue.current_mult1 <- queue.current_mult1 - 1;
	    queue.num_elem <- queue.num_elem - 1;
	    t
	   )
	 )
       else
	 (
	  if ((queue.current_mult2 > 0) & 
	      (not (Queue2.is_empty queue.queue2)))
	  then 
	    (let t =  Queue2.maximum queue.queue2 in 
	    Queue2.remove queue.queue2;     
	    Elem2.assign_in_queue2 false t;
	    if (not (Elem2.in_queue1 t)) 
	    then remove queue
	    else 
	      (queue.current_mult2 <- queue.current_mult2 - 1;
	       queue.num_elem <- queue.num_elem - 1;
	       t
	      )
	    )	   
	  else (* queue mult1 =0 and queue mult2 = 0 *)
	    ( queue.current_mult1 <- Elem2.mult1;
	      queue.current_mult2 <- Elem2.mult2;
	      remove queue)
	 )
      )



end
