## Use TLC with command line

### Reference & Link

#### reference

* [tla book (ch14)](https://research.microsoft.com/en-us/um/people/lamport/tla/book.html)
* [web site](https://research.microsoft.com/en-us/um/people/lamport/tla/tlc.html)

#### binaries

* [tool download](http://research.microsoft.com/en-us/downloads/41b4a0aa-5fad-4118-916a-45ed9fd48bf0/default.aspx)

Here, you can use [TLA+ toolbox](https://research.microsoft.com/en-us/um/people/lamport/tla/toolbox.html#downloading) which is based on eclipse IDE. But in this page is talking about CLI usage.

### Download & Setup

Here is my configuration example.

~~~
DOWNLOAD="$HOME/tools/tla/tla"
unzip -d $DOWNLOAD/tools/tla
alias tlc='java -Xmx512m -cp $HOME/tools/tla/tla tlc2.TLC -workers 2'
alias tlasany='java -Xmx512m -cp $HOME/tools/tla/tla tla2sany.SANY'
~~~

Now, you can execute sany check and TLC via `tlc` and `tlasany`.

### Run tlc.

Running tlc requires configuration file as `<SPEC_NAME>.cfg`. For example, if you would like to run `tlc increment.tla` you need to prepare `increment.cfg` in the same directory or specify it via `-config`.

~~~
$ cat increment.cfg 
SPECIFICATION Spec
~~~

Only online above makes it work. So, you can add configuration after the line. For example,

~~~
$ cat increment.cfg 
SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
~~~
