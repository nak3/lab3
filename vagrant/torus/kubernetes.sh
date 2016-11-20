#!/bin/bash
yum -y install --enablerepo=updates-testing kubernetes
yum -y install etcd iptables

IPADDR=`hostname -I | cut -f1 -d' '`
echo "${IPADDR}	fed-master
${IPADDR}	fed-node" >> /etc/hosts


cat <<EOF >/etc/kubernetes/config
# Comma separated list of nodes in the etcd cluster
KUBE_MASTER="--master=http://fed-master:8080"

# logging to stderr means we get it in the systemd journal
KUBE_LOGTOSTDERR="--logtostderr=true"

# journal message level, 0 is debug
KUBE_LOG_LEVEL="--v=0"

# Should this cluster be allowed to run privileged docker containers
KUBE_ALLOW_PRIV="--allow-privileged=false"
EOF

cat <<EOF >/etc/kubernetes/apiserver
# The address on the local server to listen to.
KUBE_API_ADDRESS="--address=0.0.0.0"

# Comma separated list of nodes in the etcd cluster
KUBE_ETCD_SERVERS="--etcd-servers=http://127.0.0.1:4001"

# Address range to use for services
KUBE_SERVICE_ADDRESSES="--service-cluster-ip-range=10.3.0.0/24"

# Add your own!
KUBE_API_ARGS=""
EOF

sed -i -e "s/ETCD_LISTEN_CLIENT_URLS=\"http\:\/\/localhost:2379\"/ETCD_LISTEN_CLIENT_URLS=\"http\:\/\/0.0.0.0:4001\"/g" /etc/etcd/etcd.conf

mkdir -p /var/run/kubernetes
chown kube:kube /var/run/kubernetes
chmod 750 /var/run/kubernetes

for SERVICES in etcd kube-apiserver kube-controller-manager kube-scheduler; do
	systemctl restart $SERVICES
	systemctl enable $SERVICES
done


### NODE ####

cat <<EOF >/root/node.json
{
    "apiVersion": "v1",
    "kind": "Node",
    "metadata": {
        "name": "fed-node",
        "labels":{ "name": "fed-node-label"}
    },
    "spec": {
        "externalID": "fed-node"
    }
}
EOF

kubectl create -f /root/node.json

cat <<EOF >/etc/kubernetes/kubelet 
###
# Kubernetes kubelet (node) config

# The address for the info server to serve on (set to 0.0.0.0 or "" for all interfaces)
KUBELET_ADDRESS="--address=0.0.0.0"

# You may leave this blank to use the actual hostname
KUBELET_HOSTNAME="--hostname-override=fed-node"

# location of the api-server
KUBELET_API_SERVER="--api-servers=http://fed-master:8080"

# Add your own!
#KUBELET_ARGS=""
EOF

for SERVICES in kube-proxy kubelet docker; do 
    systemctl restart $SERVICES
    systemctl enable $SERVICES
done


### torus flexvolume plugin ###
mkdir -p /usr/libexec/kubernetes/kubelet-plugins/volume/exec/coreos.com~torus/
cp /home/vagrant/work/src/github.com/coreos/torus/bin/torusblk /usr/libexec/kubernetes/kubelet-plugins/volume/exec/coreos.com~torus/torus
systemctl restart kubelet
