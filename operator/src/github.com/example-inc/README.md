How to start new projet in this directory
---

```
PROJECT=<REPLACE HERE>
GOPATH=/home/knakayam/dev/lab3/operator/

mkdir -p $GOPATH/src/github.com/example-inc/

cd $GOPATH/src/github.com/example-inc/
operator-sdk new $PROJECT

cd $PROJECT

operator-sdk add api --api-version=app.example.com/v1alpha1 --kind=AppService
operator-sdk add controller --api-version=app.example.com/v1alpha1 --kind=AppService
```
