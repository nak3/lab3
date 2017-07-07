

### Build ARM
~~~
# $GOBIN/packer build --var-file=variables.json
~~~

### Create image

~~~
RESOURCEGROUP=
IMAGE_ID=
IMAGE_NAME=torusdev
# az image create --resource-group ${RESOURCEGROUP} \
  --name ${IMAGE_NAME} \
   --os-type linux \
  --source ${IMAGE_ID}
~~~

