FROM fedora:latest

RUN yum -y install golang
WORKDIR /app
COPY  server server1.key server1.pem .

CMD ./server
