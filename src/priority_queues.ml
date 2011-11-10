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
