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

// Train Entity
sig Train {
	cars : some Car
}
var sig Connected in Train {}

one sig head, tail in Car {}

// Track Entity
sig Track {
	vss : some VSS // Each track is composed of at least one VSS
}

// VSS Entity
sig VSS {
	successor : lone VSS, // Each VSS can have a successor
}

one sig begin, end in VSS {}

// Car Entity
sig Car {
	var position : one VSS, // Each car has to be in a (varying) VSS
	succ : lone Car // Each car can have a successor
}

// 3 Kinds of State
var sig Free, Occupied, Unknown in VSS {}

fact Multiplicities {
	vss in Track one -> some VSS
	cars in Train one -> some Car
}

// The set Cars must be equal to head + head.*succ
fact linearTrain {
	Car in head.*succ
	succ in (Car - tail) one -> one (Car - head)
		
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

run {} for 5 but exactly 1 Train, exactly 6 VSS, exactly 5 Car


























