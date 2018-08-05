#!/bin/bash

sudo -u hdfs hdfs dfs -mkdir /hadoop/tmp/
sudo -u hdfs hdfs dfs -chmod 777 /hadoop/tmp/
sudo -u hdfs hdfs dfs -mkdir /tmp/
sudo -u hdfs hdfs dfs -chmod 777 /tmp/
sudo -u hdfs hdfs dfs -mkdir -p /hadoop/yarn/app-logs
sudo -u hdfs hdfs dfs -chmod 777 /hadoop/yarn/app-logs
sudo -u hdfs hdfs dfs -mkdir -p /user/knakayam
sudo -u hdfs hdfs dfs -mkdir -p /user/root
sudo -u hdfs hdfs dfs -chown knakayam:knakayam /user/knakayam
sudo -u hdfs hdfs dfs -chown root:root /user/root

