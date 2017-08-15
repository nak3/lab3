#!/bin/bash

GOTAR=go1.8.3.linux-amd64.tar.gz

if [ -e $GOTAR ];then
  echo "$GOTAR already exists"
  exit 0
fi

wget https://storage.googleapis.com/golang/${GOTAR}
sudo tar -C /usr/local -xzf /home/knakayam/${GOTAR}
export PATH=$PATH:/usr/local/go/bin
