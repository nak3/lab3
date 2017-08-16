## preparation

### subscription manager

~~~
ansible-vault create roles/rh_subscription/vars/user.yml
~~~

edit the user.xml as below key-value pair:

~~~
---
user: xxx
password: xxxx
~~~

### Run

~~~
ansible-playbook site.yml --ask-vault-pass
~~~
