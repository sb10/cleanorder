package main

type block struct{ start, end int }

type funcBlock struct {
	key        string
	start, end int
	recvType   string
	isMethod   bool
}

// incidentalTypeInfo tracks which types are considered incidental: types that
// have no constructors or methods and whose only users are methods whose
// receiver types are not declared in this file. Such types are emitted
// immediately before their first user rather than in the main type section.
