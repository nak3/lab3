package main

import (
	"context"
	"crypto/tls"
	"fmt"
	"net"
	"net/http"
)

const (
	target = "http://test.exapmle.com:8080"
)

var dialContext = (&net.Dialer{}).DialContext

func main() {
	tr := &http.Transport{
		TLSClientConfig: &tls.Config{},
		DialContext: func(ctx context.Context, network, addr string) (conn net.Conn, e error) {
			addr = "127.0.0.1:8080"
			fmt.Printf("addr is: %+v\n", addr)     // output for debug
			fmt.Printf("target is: %+v\n", target) // output for debug
			return dialContext(ctx, network, addr)
		}}

	req, err := http.NewRequest(
		http.MethodGet,
		target,
		nil,
	)
	if err != nil {
		panic(err)
	}

	resp, err := tr.RoundTrip(req)
	if err != nil {
		panic(err)
		return
	}
	fmt.Printf("%+v\n", resp) // output for debug
}
