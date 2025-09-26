package main

type block struct{ start, end int }

type funcBlock struct {
	key        string
	start, end int
	recvType   string
	isMethod   bool
}
