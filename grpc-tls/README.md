### 

```
oc create deployment --image=quay.io/nak3/grpc-tls grpc-tls-test
oc expose deployment.apps/grpc-tls-test --port=50051
oc expose service/grpc-tls-test
```

```
oc edit routes grpc-tls-test  
```

```
  tls:
    termination: passthrough
```
