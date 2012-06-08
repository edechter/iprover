(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2012 Konstantin Korovin and The University of Manchester. 
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




(* ******************************************************************
 * N-ary priority queues                                            *
 ********************************************************************)

(* A bare element module with only the type and no operations, those
   are given in a separate module at runtime *)
module type Elem0 =
sig 
  type t 
end


(* An element in a priority queue *)
module type ElemN = 
sig

  (* The type of an element in the queue *)
  type t

  (* A comparison function between two elements for each queue *)
  val compare : t -> t -> int

  (* A flag for membership of an element in each queue *)
  val in_queue : t -> bool

  (* A function setting the membership flag for each queue *)
  val assign_in_queue : bool -> t -> unit

  (* The multiplier for each queue *)
  val mult : int
    
end

(* An n-ary priority queue *)
module QueueN (E : Elem0) =
struct 
  
  (* The type of the elements in the queues *)
  type elt = E.t
      
  (* The data structure for one queue *)
  type queue = { 
    
    (* The module of elements in the queue *)
    mutable m_elem : (module ElemN with type t = elt);
    
    (* The queue of elements *) 
    mutable queue : Heap.ImperativeGen(E).t;
    
    (* The counter for the number of elements taken from the queue *)
    mutable mult : int 
      
  }
      
      
  (* The data structure for all n queues *)
  type t = { 
    
    (* The list of queues *) 
    mutable queues : queue list; 
    
    (* Try to count the number of unique elements in the queues *)
    mutable num_elem : int 

  }
      

  (* All queues are empty *)
  exception Empty 
    
    
  (* Create n queues *)
  let create init_size elems = 
    
    (* Local module binding at outermost level *)
    let module H = Heap.ImperativeGen(E) in
    
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
		  (module E : Heap.Ordered with type t = elt) 
		  init_size;

	      (* Initialise modulus counter *)
	      mult = 0 

	    })
	  elems;

      (* Initialise counter of elements *)
      num_elem = 0 }


  (* The number of elements in the queues *)
  let num_elem { num_elem } = num_elem

  (* Add an element to all queues *)
  let add_all ({ queues = queue_n } as q) elem = 

    (* Local module binding at outermost level *)
    let module H = Heap.ImperativeGen(E) in

    (* Add element to all queues *)
    List.iter 
      (function { m_elem; queue; _ } -> 

	(* Get module from value *)
	let module E = (val m_elem : ElemN with type t = elt) in 
	
	(* Element not already in queue, queue ratio must not be 0 *)
	if not (E.in_queue elem) && E.mult > 0 then

	  (

	    (* Add element to queue *)
	    H.add queue elem;

	    (* Flag element as in queue *)
	    E.assign_in_queue true elem

	  ))
      queue_n;
    
    (* Increment counter of elements in queue *)
    q.num_elem <- succ q.num_elem
    

  (* TODO: Create function add_some that adds to some queues only and
     correctly changes the num_elem counter, that is, does not count
     duplicates *)
      

  (* All queues are empty? *)
  let is_empty { queues = queue_n } = 

    (* Local module binding at outermost level *)
    let module H = Heap.ImperativeGen(E) in
    
    (* All queues are empty? *)
    List.for_all
      (function { queue } -> H.is_empty queue)
      queue_n


  (* Clean queues *)
  let clean init_size { queues = queue_n } =
  
    (* Local module binding at outermost level *)
    let module H = Heap.ImperativeGen(E) in

    List.iter
      (function { m_elem; queue } as q -> 

	(* Get module from value *)
	let module E = (val m_elem : ElemN with type t = elt) in 

	(* Flag all elements in queue as not in queue *)
	H.iter (E.assign_in_queue false) queue;

	(* Recreate queue *)
	q.queue <- 
	  H.create (module E : Heap.Ordered with type t = elt) init_size)
      queue_n


  (* Remove first element from the next priority queue *)
  let rec remove' ({ queues = queue_n; num_elem } as all_q) = 
    
    (* Local module binding at outermost level *)
    let module H = Heap.ImperativeGen(E) in function 

      (* No element to remove from any queue?

	 Not every queue is empty, this has to be checked by the
	 calling function, otherwise we will loop infinitely. *)
      | [] -> 

	(* Format.eprintf "No elements available in any queue@."; *)

	(* Reset modulus counters in all queues to their maximum *)
	List.iter
	  (function ({ m_elem } as q) -> 
	    let module E = (val m_elem : ElemN with type t = elt) in 
	    q.mult <- E.mult)
	  queue_n;

	(* All queues are empty? *)
	if is_empty all_q then 
	  
	  (* Raise exception *)
	  raise Empty 
	    
	else

	  (* Restart search for element to remove *)
	  remove' all_q queue_n

      (* First queue is not empty and the modulus counter is not 0? *)
      | ({ queue; m_elem; mult } as q) :: tl 
	  when mult > 0 && not (H.is_empty queue) -> 
	
	(
	  
	  (* Format.eprintf 
	    "Removing from queue %d@." 
	    ((List.length queue_n) - (List.length tl)); *)

	  (* Module for elements in this queue *)
	  let module E = (val m_elem : ElemN with type t = elt) in 

	  (* Take first element from the queue *)
	  let elem = H.pop_maximum queue in
	  
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
	    
	    (

	      (* Format.eprintf 
		"Element is not queue@."; *)
	      
	      (* Remove next element from this queue *)
	      remove' all_q (q :: tl)

	    )
	      
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
  


(* ******************************************************************
 * Binary priority queues                                           *
 ********************************************************************)


module type Elem2 = sig
  type t
  val compare1           : t -> t -> int
(* is used for checking whether t is in queue1*)
(* assuming it is stored in t as a parameter  *)
  val in_queue1          : t -> bool
  val assign_in_queue1   : bool -> t -> unit
  val mult1              : int
  val compare2           : t -> t -> int
  val mult2              : int
  val in_queue2          : t -> bool
  val assign_in_queue2   : bool -> t -> unit
end


(* after element is added it is always in both queues *)
(* if is was in one of the queues the it is not added again to this queue *)
(* if element is removed it is first checked is it is in the other queue *)
(* if not then it is discarded not affecting the ratio *)
(* queue is empty if at least one of the queues is empty*)

module Queue2(Elem2:Elem2) = struct

  module Queue1Elem = 
    struct
      type t      = Elem2.t
      let compare = Elem2.compare1
    end
  module Queue1 = Heap.Imperative (Queue1Elem) 

  module Queue2Elem = 
    struct
      type t      = Elem2.t
      let compare = Elem2.compare2
    end
  module Queue2 = Heap.Imperative (Queue2Elem) 


  type t = {mutable queue1        : Queue1.t; 
	    mutable queue2        : Queue2.t; 
	    mutable current_mult1 : int;
	    mutable current_mult2 : int;
	    mutable num_elem : int
	  }

  let create init_size = 
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
