// Track Entity
sig Track {
	vss : some VSS, // Each track is composed of at least one VSS (other than the beginning and the end)
	begin : one Begin, // Each track has a beginning VSS
	end : one End // Each track has an ending VSS
}

// VSS Entity - components of a track
sig VSS {
	successor : lone VSS // Each VSS can have a successor VSS
}
// Sets that define the Start and finish VSSs of the Track
sig Begin, End extends VSS {}

// VSSs can have 3 types of occupancy states
var sig Free, Occupied, Unknown in VSS {}

// Train Entity
sig Train {
	cars : some Car, // Each train has at least one Car (other than the Head - locomotive -, and the tail - last car)
	head : one Head, // Each train has only one Head (locomotive)
	tail : one Tail, // Each train has only one Tail (end of the train)
}

// All trains have 3 types of States:
/*
 	Incomplete - train in which there as been a separation between cars
 	Offline - train whose communication with the control center has suffer some kind of failure
	Fully operational - train that doesn't fall in any of the 2 above states: 
					   we decided that it would be the default initial state for all trains and as such did not create one Set specifically for this state
*/
var sig Incomplete, Offline in Train {}

// Car Entity - components of the train
sig Car {
	var position : one VSS, // Each car has to be in a (varying) VSS
	succ : lone Car // Each car can have a successor
}

// Sets that define the cars the are the first and last cars of a train
sig Head, Tail extends Car {}


fact Multiplicities {
	// One VSS can only belong to one track
	vss in Track one -> some VSS
	// One beginning VSS and one ending VSS can only belong to one Track
	begin in Track one -> one Begin
	end in Track one -> one End
	// One car can only belong to one train
	cars in Train one -> some Car
	// One head Car and one tail car can only belong to one Train
	head in Train one -> one Head
	tail in Train one -> one Tail
}

// Each Train forms a single line from Head to Tail
fact linearTrain {
	// All cars and the tail are a succesor of the head
	all t:Train | t.cars in t.head.*succ and t.tail in t.head.*succ
	// The tails have no successore
	no Tail.succ	
} 

// Each Track forms a single line between beggining and ending VSSs
fact linearTrack {
	// All VSSs including the last one are successors of the beginning one
	all t:Track | t.vss in t.begin.*successor and t.end in t.begin.*successor
	// The last VSS has no successors
	no End.successor
} 

// A VSS can only have one state at once
// A Train can only be in one state at once: Online and Complete, Incomplete or Offline
fact onlyOneState {
	always ({
		no Free & Occupied & Unknown
		no Free & Occupied 
		no Occupied & Unknown
		no Free & Unknown
		--all v:VSS | v in (Free + Occupied + Unknown)
	})
	always ({
		no Incomplete & Offline & (Train - Incomplete - Offline)
		no Incomplete & Offline
		no Incomplete & (Train - Incomplete - Offline)
		no Offline & (Train - Incomplete - Offline)
	})
}


// Initial state of the system
fact Init {

	// All Trains are connected
	no Incomplete
	no Offline
	all c1, c2:Car | c1->c2 in succ implies c1.position = c2.position.successor

	// Initially there is no more than one car in the same VSS
	position in Car lone -> one VSS
	// All train should have at least one car between the head and the tail
--	all t: Train | some (t.cars - t.head - t.tail)

	// VSS's are either free or occupied
	Occupied = Car.position
	Free = VSS - Car.position
	no Unknown
}

// A car cannot be in a vss that is in front of the vss of the car in front of it
fact noTrainSelfCollision {
	always (all c:Car | not c.position in succ.c.position.*successor)
}

// No operation predicate
pred nop {
	position' = position
	Incomplete' = Incomplete
	Offline' = Offline
	Free' = Free
	Occupied' = Occupied
	Unknown' = Unknown
}

// Movement of the train
pred move [t: Train] {
	// Guard
	no t.head.position & End // Train has not reached the end of the track
	t.head.position.successor in Free  // The VSS in front of the head is a free VSS, otherwise it cannot move

	// Effect - All cars of the train move one VSS, independently of its state
	all c : t.cars | c.position' = c.position.successor
	

	// if Train is both complete and online
	no (t & (Incomplete + Offline)) implies {
		// The Free VSSs are all those that are not unknown and not occupied by Online or Incomplete cars
		Free' = VSS - Unknown - (Train-Offline).cars.position'
		// The Occupied VSS are all those occupied by Online or Incomplete trains except those VSS known to be unknown
		Occupied' = (Train - Offline).cars.position' - Unknown
		Unknown' = Unknown
	}

	// if Train is Offline
	t in Offline implies {
		// Frame Conditions
		// As the train is Offline and there is no communication with the MAs, all VSS states remain unchanged
		Unknown' = Unknown
		Free' = Free
		Occupied' = Occupied
	}

	// if Train is Incomplete
	t in Incomplete implies {
		all c: t.cars | t.tail in c.*succ implies (Unknown' = Unknown + c.position')

		Free' = VSS - Unknown - Train.cars.position'
		Occupied' = VSS & Train.cars.position' - Unknown
		
	}

	// General Frame conditions
	all c: (Train - t).cars | c.position' = c.position
	Incomplete' = Incomplete
	Offline' = Offline

}

// Disconnection of a train
pred loseCar [t: Train, c: Car] {
	// Guard
	t not in Incomplete
	c in t.cars
	not c in Head
	
	
	
	// Effect
	Incomplete' = Incomplete + t
	// c will lose succ
	c.succ' = none
	-- t.cars' = t.cars - c.*succ
	// the vss of c and the cars in front of it will become unknown
	// Unknown' = Unknown + 

	// Frame conditions
	Train.cars.position' = Train.cars.position	
}

pred loseConnection [t: Train] {
	// Guard
	t not in Offline

	// Effects
	// Train becomes offline
	Offline' = Offline + t
	// Remove train cars' vss from Occupied
	Occupied' = Occupied - t.cars.position
	// Add train cars' vss to Unknown
	Unknown' = Unknown + t.cars.position

	// Frame conditions
	all c: Car | c.position' = c.position
	Incomplete' = Incomplete
	Free' = Free

	
}

// Behaviour of the system
fact Traces {
	always (
		nop 
		or (some t:Train | move[t]) 
	 	or (some t: Train | loseConnection[t])
	)
}

// Goal - No 2 trains in the same VSS
assert fullSafety {
	always (all t1, t2: Train | t1!=t2 implies always ( no t1.cars.position & t2.cars.position))
	position in Car lone -> one VSS
}

check fullSafety

// Example run command
run traces {

	some t1, t2: Train | {
		t1 != t2
		t1.tail.position in Begin
		no Head.position & End
		eventually loseConnection[t2]
		always (loseConnection[t2] implies after move[t2] )
		eventually (no Head.position.*successor & (Free-End))
		
	}

} for 15 but 1..30 steps, exactly 2 Train, exactly 6 VSS, exactly 1 Track, exactly 4 Car
