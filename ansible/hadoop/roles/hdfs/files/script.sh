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

sudo -u hdfs hdfs dfs -chmod 777 /hadoop/tmp/
sudo -u hdfs hdfs dfs -mkdir /tmp/
sudo -u hdfs hdfs dfs -chmod 777 /tmp/
sudo -u hdfs hdfs dfs -mkdir -p /hadoop/yarn/app-logs
sudo -u hdfs hdfs dfs -chmod 777 /hadoop/yarn/app-logs
sudo -u hdfs hdfs dfs -mkdir -p /user/knakayam
sudo -u hdfs hdfs dfs -mkdir -p /user/root
sudo -u hdfs hdfs dfs -chown knakayam:knakayam /user/knakayam
sudo -u hdfs hdfs dfs -chown root:root /user/root

