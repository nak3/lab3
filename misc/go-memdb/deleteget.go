package main

import (
	"fmt"
	"github.com/hashicorp/go-memdb"
)

type TestObject struct {
	ID  string
	Foo string
	Qux []string
}

func main() {

	type node struct {
		mode     uint32
		filename string
	}

	// Create the DB schema
	schema := &memdb.DBSchema{
		Tables: map[string]*memdb.TableSchema{
			"path": &memdb.TableSchema{
				Name: "path",
				Indexes: map[string]*memdb.IndexSchema{
					"id": &memdb.IndexSchema{
						Name:    "id",
						Unique:  true,
						Indexer: &memdb.StringFieldIndex{Field: "filename"},
					},
				},
			},
		},
	}

	// Create a new data base
	db, err := memdb.NewMemDB(schema)
	if err != nil {
		panic(err)
	}

	// Create a write transaction
	txn := db.Txn(true)

	// Insert a new person
	p1 := &node{1, "/test"}
	p2 := &node{1, "/test/abc"}
	p3 := &node{1, "/abc"}

	if err := txn.Insert("path", p1); err != nil {
		panic(err)
	}
	if err := txn.Insert("path", p2); err != nil {
		panic(err)
	}
	if err := txn.Insert("path", p3); err != nil {
		panic(err)
	}

	// Commit the transaction
	txn.Commit()

	// Delete
	txn = db.Txn(true)
	num, err := txn.DeleteAll("path", "id_prefix", "/test")
	if err != nil {
		panic(err)
	}
	fmt.Printf("Deleted %d of paths \n", num)
	txn.Commit()

	// Create read-only transaction
	txn = db.Txn(false)
	defer txn.Abort()

	// Lookup by path
	raw, err := txn.Get("path", "id_prefix", "/abc")
	if err != nil {
		fmt.Printf("Not found: %v \n", err)
	}

	for {
		result := raw.Next()
		if result == nil {
			break
		}
		// Show getting result
		fmt.Printf("Hello %v!", result.(*node))
	}
}
