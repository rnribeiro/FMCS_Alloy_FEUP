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
	tail : one Tail
}
var sig Connected in Train {}

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
	// All VSS are Free
	no (Occupied + Unknown) and VSS = Free

	// All Trains are connected
	Train = Connected
}

// Goal - No 2 trains in the same VSS
assert fullSafety {
--	position in Train lone -> one VSS
}

run {} for 1 but exactly 3 Train, exactly 6 VSS, exactly 10 Car


























