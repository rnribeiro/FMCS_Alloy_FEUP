/*
extends -> is a, subset of a parent, siblings are disjoint

Top-level signatures are disjoint

Facts specify assumptions

lone 0..1
some 1..*


*/

// Train Entity
sig Train {
	/* cars : some Car // each train is composed of at least one car*/
	var position : one VSS
}
var sig Connected in Train {}

// Track Entity
sig Track {
	vss : some VSS // Each track is composed of at least one VSS
}

// VSS Entity
sig VSS {
	successor : lone VSS, // Each VSS can have a successor
}

one sig begin, end in VSS {}

/* Car Entity
sig Car {
	var position : one VSS, // Each car has to be in a (varying) VSS
	succ : lone Car // Each car can have a successor
}
*/
	
// 3 Kinds of State
var sig Free, Occupied, Unknown in VSS {}

fact Multiplicities {
	vss in Track one -> some VSS

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
	position in Train lone -> one VSS
}



run {} for 5 but exactly 3 Train, exactly 6 VSS



























