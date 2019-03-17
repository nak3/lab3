package main

import (
	"crypto/tls"
	"crypto/x509"
	"fmt"
	"io/ioutil"
	"os"
	"os/signal"

	"github.com/Shopify/sarama"
)

func NewTLSConfig(clientCertFile, clientKeyFile, caCertFile string) (*tls.Config, error) {
	tlsConfig := tls.Config{}

	// Load client cert
	cert, err := tls.LoadX509KeyPair(clientCertFile, clientKeyFile)
	if err != nil {
		return &tlsConfig, err
	}
	tlsConfig.Certificates = []tls.Certificate{cert}

	// Load CA cert
	caCert, err := ioutil.ReadFile(caCertFile)
	if err != nil {
		return &tlsConfig, err
	}
	caCertPool := x509.NewCertPool()
	caCertPool.AppendCertsFromPEM(caCert)
	tlsConfig.RootCAs = caCertPool

	tlsConfig.BuildNameToCertificate()
	return &tlsConfig, err
}

const (
	topic       = "test"
	certsDir    = "tools/kafka/cert/test/"
	kafkaBroker = "localhost:9093"
)

func main() {
	config := sarama.NewConfig()
	config.Net.TLS.Enable = true

	home := os.Getenv("HOME")

	tlsConfig, err := NewTLSConfig(
		fmt.Sprintf("%s/%s/client.cer.pem", home, certsDir),
		fmt.Sprintf("%s/%s/client.key.pem", home, certsDir),
		fmt.Sprintf("%s/%s/server.cer.pem", home, certsDir),
	)
	if err != nil {
		panic(err)
	}

	config.Net.TLS.Config = tlsConfig
	config.Consumer.Return.Errors = true

	// Specify brokers address. This is default one
	brokers := []string{kafkaBroker}

	// Create new consumer
	master, err := sarama.NewConsumer(brokers, config)
	if err != nil {
		panic(err)
	}

	defer func() {
		if err := master.Close(); err != nil {
			panic(err)
		}
	}()

	consumer, err := master.ConsumePartition(topic, 0, sarama.OffsetOldest)
	if err != nil {
		panic(err)
	}

	signals := make(chan os.Signal, 1)
	signal.Notify(signals, os.Interrupt)

	// Count how many message processed
	msgCount := 0

	// Get signnal for finish
	doneCh := make(chan struct{})
	go func() {
		for {
			select {
			case err := <-consumer.Errors():
				fmt.Println(err)
			case msg := <-consumer.Messages():
				msgCount++
				fmt.Println("Received messages", string(msg.Key), string(msg.Value))
			case <-signals:
				fmt.Println("Interrupt is detected")
				doneCh <- struct{}{}
			}
		}
	}()

	<-doneCh
	fmt.Println("Processed", msgCount, "messages")
}
