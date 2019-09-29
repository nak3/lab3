package main

import (
	"fmt"
	"net/http"
)

func rootHandler(w http.ResponseWriter, r *http.Request) {
	fmt.Printf("%+v\n", r) // output for debug
}

func main() {
	http.HandleFunc("/", rootHandler)
	panic(http.ListenAndServe(":8080", nil))
}
