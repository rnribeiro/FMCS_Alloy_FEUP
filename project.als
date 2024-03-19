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

// Track Entity
sig Track {
	vss : some VSS // Each track is composed of at least one VSS
}

// VSS Entity
sig VSS {
	successor : lone VSS, // Each VSS can have a successor
	var state : one State // Each VSS must have only one (varying) state
}

/* Car Entity
sig Car {
	var position : one VSS, // Each car has to be in a (varying) VSS
	succ : lone Car // Each car can have a successor
}
*/

// VSS State Entity
abstract sig State {}
	
// 3 Kinds of State
one sig Free, Occupied, Unknown extends State {}

fact Multiplicities {
	-- cars in Train one -> some Car
	vss in Track one -> some VSS
	successor in VSS one -> lone VSS
	-- succ in Car one -> lone Car
	
}


// Goal - No 2 trains in the same VSS
assert fullSafety {
	-- goal: position in Train lone -> one VSS
	always (all t:Train, v: VSS
}


run {}



























