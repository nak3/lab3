package main

import (
	"fmt"
	"reflect"
	"strings"

	"github.com/hashicorp/go-memdb"
)

type TestObject struct {
	ID  string
	Foo string
	Qux []string
	Zod map[string]string
}

// StringSliceFieldIndex is used to extract a field from an object
// using reflection and builds an index on that field.
type MultiSliceFieldIndex struct {
	Field     string
	Lowercase bool
}

func (s *MultiSliceFieldIndex) FromArgs(args ...interface{}) ([]byte, error) {
	fmt.Printf("FromArgs: %v \n", args)
	// if len(args) != 1 {
	// 	return nil, fmt.Errorf("must provide only a single argument")
	// }
	arg, ok := args[0].(string)
	if !ok {
		return nil, fmt.Errorf("argument must be a string: %#v", args[0])
	}
	if s.Lowercase {
		arg = strings.ToLower(arg)
	}
	// Add the null character as a terminator
	arg += "\x00"
	return []byte(arg), nil
}

func (s *MultiSliceFieldIndex) FromObject(obj interface{}) (bool, [][]byte, error) {
	fmt.Printf("FromObject: %v \n", obj)

	v := reflect.ValueOf(obj)
	v = reflect.Indirect(v) // Dereference the pointer if any

	fv := v.FieldByName(s.Field)
	if !fv.IsValid() {
		return false, nil,
			fmt.Errorf("field '%s' for %#v is invalid", s.Field, obj)
	}

	if fv.Kind() != reflect.Slice || fv.Type().Elem().Kind() != reflect.String {
		return false, nil, fmt.Errorf("field '%s' is not a string slice", s.Field)
	}

	length := fv.Len()
	fmt.Printf("fv: %#v \n", fv)

	vals := make([][]byte, 0, length)
	for i := 0; i < fv.Len(); i++ {
		val := fv.Index(i).String()
		if val == "" {
			continue
		}

		if s.Lowercase {
			val = strings.ToLower(val)
		}

		// Add the null character as a terminator
		val += "\x00"
		vals = append(vals, []byte(val))
	}
	if len(vals) == 0 {
		return false, nil, nil
	}
	fmt.Printf("vals: %#v \n", vals)

	return true, vals, nil
}

func main() {

	schema := &memdb.DBSchema{
		Tables: map[string]*memdb.TableSchema{
			"main": &memdb.TableSchema{
				Name: "main",
				Indexes: map[string]*memdb.IndexSchema{
					"id": &memdb.IndexSchema{
						Name:    "id",
						Unique:  true,
						Indexer: &memdb.StringFieldIndex{Field: "ID"},
					},
					"foo": &memdb.IndexSchema{
						Name:    "foo",
						Indexer: &memdb.StringFieldIndex{Field: "Foo"},
					},
					"qux": &memdb.IndexSchema{
						Name: "qux",
						//						Indexer: &memdb.StringSliceFieldIndex{Field: "Qux"},
						Indexer: &MultiSliceFieldIndex{Field: "Qux"},
					},
					"zod": &memdb.IndexSchema{
						Name:    "zod",
						Indexer: &memdb.StringMapFieldIndex{Field: "Zod"},
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
	obj1 := &TestObject{
		ID:  "my-object",
		Foo: "abc",
		Qux: []string{"abc1", "abc2"},
		Zod: map[string]string{
			"Role":          "Server",
			"instance_type": "m3.medium",
			"":              "asdf",
		},
	}
	obj2 := &TestObject{
		ID:  "my-object",
		Foo: "abc",
		Qux: []string{"abc1"},
		Zod: map[string]string{
			"Role":          "Server",
			"instance_type": "m3.medium",
			"":              "asdf",
		},
	}

	err = txn.Insert("main", obj1)
	err = txn.Insert("main", obj2)
	if err != nil {
		panic(err)
	}
	txn.Commit()

	txn = db.Txn(false)
	result, err := txn.Get("main", "qux", "abc1")
	if err != nil {
		panic(err)
	}
	txn.Commit()

	raw := result.Next()

	fmt.Printf("reulst: %v \n", raw.(*TestObject))
}
