#!/bin/bash

if [ -e /hadoop ];then
  echo "/hadoop already exists"
  exit 0
fi

mkdir /hadoop
mkdir /hadoop/hdfs
chown hdfs:hadoop /hadoop/hdfs/
chmod 755 /hadoop/hdfs/
mkdir /hadoop/yarn
chown yarn:hadoop /hadoop/yarn/
chmod 755 /hadoop/yarn/
mkdir /hadoop/tmp/
chmod 777 /hadoop/tmp/

# initialize
sudo -u hdfs hdfs namenode -format
