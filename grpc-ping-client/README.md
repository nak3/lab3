### To deploy server

```
cd $GOPATH/src/knative.dev/serving
ko apply -f test/test_images/grpc-ping/service.yaml 
```

### To run grpc client

```
go run grpc-ping-client.go -addr grpc-ping-test-image.default.apps.dirty.aws.oshift.net:443
```

This example is based on https://github.com/grpc/grpc-go/tree/master/examples/features/encryption
