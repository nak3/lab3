How to run
---
~~~
git clone https://github.com/nak3/lab3.git
cd lab3/vagrant/hadoop
vagrant up

vagrant ssh-config --host cdh5 | tee -a ~/.ssh/config
vagrant ssh-config --host cdh5 | sudo tee -a /root/.ssh/config

// TODO: replace IP address
echo "192.168.121.64 cdh5" | sudo tee -a /etc/hosts
cd lab3/ansible/hdoop
sudo ansible-playbook -i inventory site.yml
~~~
