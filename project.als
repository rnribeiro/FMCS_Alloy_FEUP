/*
extends -> is a, subset of a parent, siblings are disjoint

Top-level signatures are disjoint

Facts specify assumptions

lone 0..1
some 1..*

// Transitive closure
^ R= R + R.R + R.R.R + R.R.R.R + ...
// Reflexive transitive closure
*R = ^R + iden

*/

// Track Entity
sig Track {
	vss : some VSS, // Each track is composed of at least one VSS
	begin : one Begin,
	end : one End
}

// VSS Entity
sig VSS {
	successor : lone VSS // Each VSS can have a successor
}
sig Begin, End extends VSS {}
// 3 Kinds of State
var sig Free, Occupied, Unknown in VSS {}

// Train Entity
sig Train {
	cars : some Car,
	head : one Head, 
	tail : one Tail,
}
var sig Incomplete, Offline in Train {}

// Car Entity
sig Car {
	var position : one VSS, // Each car has to be in a (varying) VSS
	succ : lone Car // Each car can have a successor
}
sig Head, Tail extends Car {}


fact Multiplicities {
	// One VSS can only belong to one track
	vss in Track one -> some VSS
	begin in Track one -> one Begin
	end in Track one -> one End
	// One car can only belong to one train
	cars in Train one -> some Car
	head in Train one -> one Head
	tail in Train one -> one Tail
}

// The train should form a single line from Head to Tail
fact linearTrain {
	// All cars and the tail are a succesor of the head
	all t:Train | t.cars in t.head.*succ and t.tail in t.head.*succ
	// The tails have no successore
	no Tail.succ	
} 

// Tracks form a single line from Begin to End
fact linearTrack {
	// All cars and the tail are a succesor of the head
	all t:Track | t.vss in t.begin.*successor and t.end in t.begin.*successor
	// The tails have no successore
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
	})
	always (no Incomplete & Offline & (Train - Incomplete - Offline))
}

// Initial state of the system
fact Init {

	// All Trains are connected
	no Incomplete
	no Offline
	all c1, c2:Car | c1->c2 in succ implies c1.position = c2.position.successor

	// All train start in the beginning of the track
	-- Tail.position = begin
	// No train collisions
	-- all t1, t2 : Train | no t1.cars.position & t2.cars.position

	// VSS's are either free or occupied
	Occupied = Car.position
	Free = VSS - Car.position
	no Unknown
}

// A car cannot be in a vss that is in front of the vss of the car in front of it
fact noCollision {
	all c:Car | not c.position in succ.c.position.*successor
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
	t.head.position.successor in Free  // The VSS in front of the head is a free VSS

	// Effect - All cars in any kind of train move one VSS
	all c : t.cars | c.position' = c.position.successor

	// if Train is both complete and online
	no (t & Incomplete & Offline) implies {
		Free' = VSS - Unknown - Train.cars.position'
		Occupied' = VSS & Train.cars.position' - Unknown
		Unknown' = Unknown
	}

	// if Train is Offline
	t in Offline implies {
		Unknown' = Unknown + t.cars.position'

		// Frame Conditions
		Free' = VSS - Occupied - Unknown
		Occupied' = Occupied
	}

	// if Train is Incomplete
	t in Incomplete implies {
		all c: t.cars | t.tail in c.*succ implies (Unknown' = Unknown + c.position')

		Free' = VSS - Unknown - Train.cars.position'
		Occupied' = VSS & Train.cars.position' - Unknown
		
	}

	// General Frame conditions
	all t1: Train - t | t1.cars.position' = t1.cars.position
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
	
}


fact Traces {
	always (
		nop 
		or (some t:Train | move[t]) 
	--	or (some t: Train | some c: t.cars | loseCar[t, c])
	-- 	or (some t: Train | 
	)
}


// Goal - No 2 trains in the same VSS
assert fullSafety {
	always (all t1, t2: Train | t1!=t2 implies always ( no t1.cars.position & t2.cars.position))
}
check fullSafety

run  {
--	one t: Train | t.tail.position = begin
--	all t: Train | eventually move[t]
--	some t: Train | eventually t in Offline
--	always(	all t: Offline | eventually move[t])
--	always (no Incomplete)
--	some t: Train | some c: t.cars | eventually disconnect[t, c]
} for 5 but exactly 12 VSS, exactly 2 Train, exactly 6 Car


























