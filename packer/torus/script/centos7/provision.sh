#/bin/sh

### set env values ###
PATH=$PATH:$HOME/bin
export PATH

export PATH=$PATH:$GOPATH/bin
export GOPATH=$HOME/work
export GOBIN=$GOPATH/bin

### package install ###
yum -y update
yum install -y unzip curl wget vim-minimal git make docker rkt systemd-container nbd.x86_64 strace lsof psmisc kernel-modules kernel-modules-extra aoetools perf gcc fio #golang
yum -y erase vim-minimal
yum -y install sudo vim-enhanced

### setting bash profile ###
cat <<EOF >~/.bash_profile
# .bash_profile

# Get the aliases and functions
if [ -f ~/.bashrc ]; then
        . ~/.bashrc
fi

# User specific environment and startup programs
PATH=$PATH:$HOME/bin
export PATH
export PATH=$PATH:/usr/local/go/bin

export PATH=$PATH:$GOPATH/bin
export GOPATH=$HOME/work
export GOBIN=$GOPATH/bin

alias cdtorus="cd $GOPATH/src/github.com/alternative-storage/torus"
EOF

### install latest golang ###

export VERSION=1.8.3
export OS=linux
export ARCH=amd64
wget https://storage.googleapis.com/golang/go$VERSION.$OS-$ARCH.tar.gz
tar -C /usr/local -xzf go$VERSION.$OS-$ARCH.tar.gz
export PATH=$PATH:/usr/local/go/bin


### setting /etc/hosts ###

IPADDR=`hostname -I | cut -f1 -d' '`
HOSTNAME=`hostname -f`
echo "${IPADDR} ${HOSTNAME}" >> /etc/hosts

### install torus ###

git clone https://github.com/alternative-storage/torus.git ~/work/src/github.com/alternative-storage/torus
cd ~/work/src/github.com/alternative-storage/torus; make
~/work/src/github.com/alternative-storage/torus/bin/torusctl config -C http://192.168.121.1:2379

~/work/src/github.com/alternative-storage/torus/bin/torusctl completion >  /tmp/torusctl
~/work/src/github.com/alternative-storage/torus/bin/torusblk completion >  /tmp/torusblk
~/work/src/github.com/alternative-storage/torus/bin/torusd --completion >  /tmp/torusd
cp /tmp/torusctl /usr/share/bash-completion/completions/torusctl
cp /tmp/torusblk /usr/share/bash-completion/completions/torusblk
cp /tmp/torusd /usr/share/bash-completion/completions/torusd


### enable kernel modules ###

cat <<EOF >/etc/modules-load.d/nbd.conf
nbd
EOF
cat <<EOF >/etc/modules-load.d/aoe.conf
aoe
EOF
cat <<EOF >/etc/modules-load.d/target_core_user.conf
target_core_user
EOF

systemctl restart systemd-modules-load
systemctl enable systemd-modules-load
