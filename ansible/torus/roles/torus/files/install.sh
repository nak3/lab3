#!/bin/bash

export PATH=$PATH:/usr/local/go/bin
source ~/.bash_profile
git clone https://github.com/nak3/torus-1.git $GOPATH/src/github.com/alternative-storage/torus
cd $GOPATH/src/github.com/alternative-storage/torus
make
./bin/torusctl config -C http://192.168.121.1:2379
sudo ./bin/torusctl config -C http://192.168.121.1:2379

./bin/torusctl completion >  /tmp/torusctl
./bin/torusblk completion >  /tmp/torusblk
./bin/torusd --completion >  /tmp/torusd

sudo cp /tmp/torusctl /usr/share/bash-completion/completions/torusctl
sudo cp /tmp/torusblk /usr/share/bash-completion/completions/torusblk
sudo cp /tmp/torusd /usr/share/bash-completion/completions/torusd
