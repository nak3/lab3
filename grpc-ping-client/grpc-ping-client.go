// Binary client is an example client.
package main

import (
	"context"
	"crypto/tls"
	"flag"
	"fmt"
	"log"

	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials"

	ping "./proto"
)

// TODO: Replace host or use --addr flag for the target host.
const host = "grpc-ping-test-image.default.apps.dirty.aws.oshift.net"

var addr = flag.String("addr", host+":443", "the address to connect to")

var clientTLSConfig = &tls.Config{
	InsecureSkipVerify: true,
}

func main() {
	flag.Parse()

	creds := credentials.NewTLS(clientTLSConfig)
	err := creds.OverrideServerName(host)
	if err != nil {
		log.Fatalf("failed to add hostname: %v", err)
	}

	conn, err := grpc.Dial(*addr, grpc.WithTransportCredentials(creds))
	if err != nil {
		log.Fatalf("did not connect: %v", err)
	}
	defer conn.Close()

	pc := ping.NewPingServiceClient(conn)

	want := &ping.Request{Msg: "Hello!"}
	got, err := pc.Ping(context.Background(), want)
	if err != nil {
		log.Fatalf("Couldn't send request: %v", err)
	}
	fmt.Println(got)
}
