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
	vss : some VSS // Each track is composed of at least one VSS
}

// VSS Entity
sig VSS {
	successor : lone VSS, // Each VSS can have a successor
}
one sig begin, end in VSS {}
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

// The track forms a single line between begin and end VSS's
fact linearTrack {
	VSS in begin.*successor
	successor in (VSS - end) one -> one (VSS - begin)
}

// A VSS can only have one state at once
fact onlyOneState {
	no Free & Occupied & Unknown
}

// Initial state of the system
fact Init {

	// All Trains are connected
	no Incomplete
	no Offline
	all c1, c2:Car | c1->c2 in succ implies c1.position = c2.position.successor

	// All train start in the beginning of the track
	Tail.position = begin

	// VSS's are either free or occupied
	Occupied = Car.position
	Free = VSS - Car.position
	no Unknown
}


// A car cannot be in a vss that is in front of the vss of the car in front of it
fact noCollision {
	all c:Car | not c.position in succ.c.position.*successor
}

// assert connected {
// 	// The train is connected
// 	always (all c1, c2:Car | c1->c2 in succ implies c1.position = c2.position.successor)
// }

// No operation predicate
pred nop {
	// No operation
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
	t.head.position != end
	t.head.position.successor in Free 

	// Effect if 
	all c : t.cars | c.position' = c.position.successor
	Free' = VSS - Unknown - Train.cars.position'
	Occupied' = VSS & Train.cars.position' - Unknown

	// Frame conditions
	-- Connected' = Connected
	Unknown' = Unknown
	all t1: Train - t | t1.cars.position' = t1.cars.position

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
--	position in Train lone -> one VSS
}

run  {
	all t: Train | eventually move[t]
--	some t: Train | some c: t.cars | eventually disconnect[t, c]
} for 5 but exactly 10 VSS, exactly 2 Train, exactly 6 Car


























