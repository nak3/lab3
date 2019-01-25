How to run
---
~~~
git clone https://github.com/nak3/lab3.git
cd lab3/vagrant/samba
vagrant up

vagrant ssh-config --host samba | tee -a ~/.ssh/config
vagrant ssh-config --host samba | sudo tee -a /root/.ssh/config

// TODO: replace IP address
echo "192.168.121.64 samba" | sudo tee -a /etc/hosts
~~~

Setup samba
---

### Test with `smbclient` command.

~~~
# smbclient //localhost/test
Enter SAMBA\root's password: 
Anonymous login successful
Try "help" to get a list of possible commands.
~~~

### Test with mount command

- Create a samba user

~~~
# useradd knakayam
~~~

- Add samba password

~~~
# smbpasswd -a knakayam
~~~

- mount cifs

~~~
# mount -t cifs //localhost/test /mnt -o username=test
Password for test@//localhost/test:  ******
~~~
