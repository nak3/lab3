```
GOPATH=/home/knakayam/dev/lab3/operator/
operator-sdk build nak3/app-operator
docker push nak3/app-operator

kubectl create -f deploy/service_account.yaml
kubectl create -f deploy/role.yaml
kubectl create -f deploy/role_binding.yaml
kubectl create -f deploy/crds/app_v1alpha1_appservice_crd.yaml
kubectl create -f deploy/operator.yaml
kubectl create -f deploy/crds/app_v1alpha1_appservice_cr.yaml

kubectl delete -f deploy/crds/app_v1alpha1_appservice_cr.yaml
kubectl delete -f deploy/operator.yaml
kubectl delete -f deploy/role.yaml
kubectl delete -f deploy/role_binding.yaml
kubectl delete -f deploy/service_account.yaml
kubectl delete -f deploy/crds/app_v1alpha1_appservice_crd.yaml
```
